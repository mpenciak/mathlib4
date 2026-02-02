#!/usr/bin/env python3
"""
Automatically fixes instance_reducible warnings in Mathlib.

Runs `lake build` to collect warnings, then for each unique instance:
- Locates the definition (which may be in a different file)
- Adds @[instance_reducible] attribute to the definition
- Verifies the fix worked by rebuilding

By default, only processes warnings from `local instance` or `scoped instance`
declarations. Use --global to also include regular instances.

Usage:
    python3 scripts/fix_instance_reducible.py                     # Full build, all warnings
    python3 scripts/fix_instance_reducible.py Mathlib/Foo.lean    # Build up to file, fix deps too
    python3 scripts/fix_instance_reducible.py --only Mathlib/Foo.lean  # Only fix that file
    python3 scripts/fix_instance_reducible.py --dry-run
    python3 scripts/fix_instance_reducible.py -n 7                # Only last 7 warnings
    python3 scripts/fix_instance_reducible.py --global            # Include global instances
    python3 scripts/fix_instance_reducible.py --no-verify         # Skip build verification
"""

import argparse
import os
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path


def parse_args():
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('target', nargs='?', metavar='FILE',
                        help='Build up to this file and fix warnings in it and dependencies')
    parser.add_argument('--dry-run', action='store_true',
                        help='Show what would be done without making changes')
    parser.add_argument('--global', dest='include_global', action='store_true',
                        help='Also process global (non-local/scoped) instance warnings')
    parser.add_argument('--global-only', action='store_true',
                        help='Only process global instance warnings')
    parser.add_argument('-n', type=int, default=None,
                        help='Only process the last N warnings (from end of build)')
    parser.add_argument('--no-verify', action='store_true',
                        help='Skip build verification after each file change')
    parser.add_argument('--only', metavar='FILE',
                        help='Only process warnings from this specific file (not dependencies)')
    return parser.parse_args()


def run_build(target=None):
    """Run lake build and return the output."""
    if target:
        module = file_to_module(target)
        print(f"Running lake build {module} to collect warnings...")
        result = subprocess.run(['lake', 'build', module], capture_output=True, text=True, timeout=7200)
    else:
        print("Running lake build to collect warnings...")
        result = subprocess.run(['lake', 'build'], capture_output=True, text=True, timeout=7200)
    return result.stdout + result.stderr


def parse_warnings(output, args):
    """Parse instance_reducible warnings from build output."""
    pattern = re.compile(
        r"warning: ([^:]+):(\d+):(\d+): instance `([^`]+)` must be marked"
    )

    warnings = []
    for line in output.split('\n'):
        match = pattern.search(line)
        if match:
            file_path = match.group(1)
            line_num = int(match.group(2))
            col_num = int(match.group(3))
            instance_name = match.group(4)
            warnings.append({
                'file': file_path,
                'line': line_num,
                'col': col_num,
                'instance': instance_name,
            })

    return warnings


def is_local_or_scoped(file_path, line_num):
    """Check if the attribute statement containing this warning is local or scoped.

    Traces backwards from the warning line to find 'attribute [instance]',
    then checks if 'local' or 'scoped' precedes it.
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()

            # Trace backwards to find 'attribute [instance]' or 'attribute[instance]'
            for i in range(line_num - 1, max(0, line_num - 10) - 1, -1):
                content = lines[i]
                if re.search(r'\battribute\s*\[', content):
                    # Found attribute line - check this line and the one before for local/scoped
                    if 'local' in content or 'scoped' in content:
                        return True
                    if i > 0 and ('local' in lines[i - 1] or 'scoped' in lines[i - 1]):
                        return True
                    return False
    except:
        pass
    return False


def filter_warnings(warnings, args):
    """Filter warnings based on --global / --global-only flags."""
    filtered = []
    for w in warnings:
        is_local_scoped = is_local_or_scoped(w['file'], w['line'])

        if args.global_only:
            # Only global
            if not is_local_scoped:
                filtered.append(w)
        elif args.include_global:
            # Both
            filtered.append(w)
        else:
            # Only local/scoped (default)
            if is_local_scoped:
                filtered.append(w)

    return filtered


def deduplicate_by_instance(warnings):
    """Keep only one warning per unique instance name."""
    seen = {}
    for w in warnings:
        if w['instance'] not in seen:
            seen[w['instance']] = w
    return list(seen.values())


def load_to_additive_mappings():
    """
    Load multiplicative → additive mappings from Mathlib's ToAdditive.lean.

    Returns dict mapping additive patterns to multiplicative patterns.
    """
    # Source: Mathlib/Tactic/Translate/ToAdditive.lean nameDict
    # Format there is ("mul", ["Add"]) meaning mul → Add
    # We need the reverse: Add → mul
    to_additive_path = Path('Mathlib/Tactic/Translate/ToAdditive.lean')

    if not to_additive_path.exists():
        raise FileNotFoundError(
            f"Cannot find {to_additive_path}. Run this script from the mathlib root directory.")

    content = to_additive_path.read_text()
    # Parse entries like ("mul", ["Add"]) or ("monoid", ["Add", "Monoid"])
    pattern = r'\("(\w+)",\s*\["([^"]+)"(?:,\s*"([^"]+)")?\]\)'
    mappings = {}
    for match in re.finditer(pattern, content):
        mul_name = match.group(1)
        add_parts = [match.group(2)]
        if match.group(3):
            add_parts.append(match.group(3))
        add_name = ''.join(add_parts).lower()
        # Store lowercase additive → lowercase multiplicative
        mappings[add_name] = mul_name

    if not mappings:
        raise ValueError(f"Failed to parse any mappings from {to_additive_path}")

    # Add compound words that ToAdditive derives automatically from base mappings
    # These aren't in nameDict but are generated by the word-splitting algorithm
    mappings['subtraction'] = 'division'
    mappings['negation'] = 'inversion'

    return mappings


# Cache the mappings
_TO_ADDITIVE_MAPPINGS = None


def get_to_additive_mappings():
    """Get cached ToAdditive mappings."""
    global _TO_ADDITIVE_MAPPINGS
    if _TO_ADDITIVE_MAPPINGS is None:
        _TO_ADDITIVE_MAPPINGS = load_to_additive_mappings()
    return _TO_ADDITIVE_MAPPINGS


def get_multiplicative_names(additive_name):
    """
    Convert an additive name to likely multiplicative counterparts.
    Returns a list of candidates (may be empty).

    Uses mappings from Mathlib/Tactic/Translate/ToAdditive.lean when available.
    """
    mappings = get_to_additive_mappings()
    candidates = []

    # Split name into parts and try to map each part
    # E.g., "addCommMonoid" → ["add", "Comm", "Monoid"]
    parts = re.findall(r'[a-z]+|[A-Z][a-z]*|[A-Z]+(?=[A-Z]|$)', additive_name)

    # Try single-part replacements
    for i, part in enumerate(parts):
        lower_part = part.lower()
        if lower_part in mappings:
            mul_part = mappings[lower_part]
            # Match capitalization
            if part[0].isupper():
                mul_part = mul_part.capitalize()
            new_parts = parts[:i] + [mul_part] + parts[i+1:]
            candidate = ''.join(new_parts)
            if candidate not in candidates and candidate != additive_name:
                candidates.append(candidate)

    # Try removing 'add'/'Add' prefix (for addCommMonoid → commMonoid)
    if additive_name.startswith('add') and len(additive_name) > 3:
        candidate = additive_name[3].lower() + additive_name[4:]
        if candidate not in candidates:
            candidates.append(candidate)
    if additive_name.startswith('Add') and len(additive_name) > 3:
        candidate = additive_name[3:]
        if candidate not in candidates:
            candidates.append(candidate)

    # Double replacements (for names like addZeroClass → mulOneClass)
    for c in list(candidates):
        for i, part in enumerate(re.findall(r'[a-z]+|[A-Z][a-z]*|[A-Z]+(?=[A-Z]|$)', c)):
            lower_part = part.lower()
            if lower_part in mappings:
                mul_part = mappings[lower_part]
                if part[0].isupper():
                    mul_part = mul_part.capitalize()
                parts2 = re.findall(r'[a-z]+|[A-Z][a-z]*|[A-Z]+(?=[A-Z]|$)', c)
                new_parts = parts2[:i] + [mul_part] + parts2[i+1:]
                candidate = ''.join(new_parts)
                if candidate not in candidates and candidate != additive_name:
                    candidates.append(candidate)

    return candidates


def find_definition(instance_name, warning_file):
    """
    Find the definition of an instance.

    Returns (file_path, line_num, line_content) or None if not found.

    If the instance appears to be an additive version generated by @[to_additive],
    looks for the multiplicative source definition instead.
    """
    # Get the local name (last part after final dot)
    parts = instance_name.rsplit('.', 1)
    local_name = parts[-1] if len(parts) > 1 else instance_name
    namespace = parts[0] if len(parts) > 1 else None

    # Patterns to search for the local name
    # Only def declarations need @[instance_reducible] - abbrev is already reducible,
    # and instance declarations don't need it
    # Handle all orderings of protected/noncomputable
    def make_patterns(name):
        return [
            rf'^\s*def\s+{re.escape(name)}\b',
            rf'^\s*protected\s+def\s+{re.escape(name)}\b',
            rf'^\s*noncomputable\s+def\s+{re.escape(name)}\b',
            rf'^\s*protected\s+noncomputable\s+def\s+{re.escape(name)}\b',
            rf'^\s*noncomputable\s+protected\s+def\s+{re.escape(name)}\b',
        ]

    patterns = make_patterns(local_name)

    # Check if this looks like an additive name - if so, prefer multiplicative lookup
    mul_local_names = get_multiplicative_names(local_name)
    is_likely_additive = len(mul_local_names) > 0

    # Try warning file first (most common case - definition in same file)
    result = search_file_for_def(warning_file, patterns, namespace)
    if result:
        return result

    # For qualified names like Set.Nat.fintypeIio, also try "def Nat.fintypeIio"
    # (definition might use qualified name rather than being inside namespace)
    if namespace and '.' in namespace:
        ns_parts = namespace.split('.')
        for i in range(1, len(ns_parts)):
            qualified_name = '.'.join(ns_parts[i:] + [local_name])
            result = search_file_for_def(warning_file, make_patterns(qualified_name), None)
            if result:
                return result

    # Project-wide search (skip for likely additive names - too many false matches)
    if not is_likely_additive:
        result = search_project_for_def(patterns, local_name, namespace)
        if result:
            return result

    # For additive instances: search for @[to_additive additive_name] directly
    # This avoids hardcoded additive→multiplicative mappings
    result = find_to_additive_source(warning_file, instance_name, namespace)
    if result:
        return result

    # Project-wide @[to_additive] search (for cross-file definitions)
    if is_likely_additive:
        result = search_project_for_to_additive(instance_name)
        if result:
            return result

    # Fallback: use heuristic name mappings (may be out of sync with to_additive)
    for mul_local_name in mul_local_names:
        if not mul_local_name:
            continue
        mul_namespaces = get_multiplicative_names(namespace) if namespace else [namespace]

        for mul_namespace in (mul_namespaces or [namespace]):
            result = search_file_for_def(warning_file, make_patterns(mul_local_name), mul_namespace or namespace)
            if result and has_to_additive(result[0], result[1]):
                return result

    return None


def has_to_additive(file_path, def_line):
    """Check if a definition has @[to_additive] attribute."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()

        # Check preceding lines for @[to_additive]
        for i in range(max(0, def_line - 10), def_line):
            if 'to_additive' in lines[i]:
                return True
    except:
        pass
    return False


def find_to_additive_source(file_path, additive_name, namespace=None):
    """
    Find a definition whose @[to_additive] generates the given additive name.

    This avoids hardcoded additive→multiplicative mappings by searching for
    @[to_additive additive_name] directly in the source.
    """
    local_name = additive_name.rsplit('.', 1)[-1]
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()

        # Look for @[to_additive ... local_name ...] patterns
        # Match exact name (word boundary), not substring
        pattern = rf'\bto_additive\b.*\b{re.escape(local_name)}\b'
        for i, line in enumerate(lines):
            if re.search(pattern, line):
                # Found a potential match - find the associated def (not abbrev - already reducible)
                for j in range(i, min(len(lines), i + 10)):
                    # Match def with any combination of protected/noncomputable
                    if re.match(r'^\s*(protected\s+)?(noncomputable\s+)?def\s+\w+', lines[j]) or \
                       re.match(r'^\s*noncomputable\s+protected\s+def\s+\w+', lines[j]):
                        return (file_path, j + 1, lines[j].rstrip())
    except:
        pass
    return None


def search_file_for_def(file_path, patterns, namespace=None):
    """Search a single file for definition patterns, optionally within a namespace."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()

        # Track current namespace (only actual namespaces, not sections)
        current_namespace = []
        for i, line in enumerate(lines):
            # Track namespace changes
            ns_match = re.match(r'^namespace\s+(\S+)', line)
            if ns_match:
                current_namespace.append(ns_match.group(1))
            # Only pop if ending the current namespace
            end_match = re.match(r'^end\s+(\S+)', line)
            if end_match and current_namespace and end_match.group(1) == current_namespace[-1]:
                current_namespace.pop()

            for pattern in patterns:
                if re.search(pattern, line):
                    # If namespace specified, check we're in the right one
                    if namespace:
                        full_ns = '.'.join(current_namespace)
                        if namespace == full_ns or namespace.endswith('.' + full_ns) or full_ns.endswith('.' + namespace):
                            return (file_path, i + 1, line.rstrip())
                        # Also accept if namespace matches last component
                        if current_namespace and namespace.split('.')[-1] == current_namespace[-1]:
                            return (file_path, i + 1, line.rstrip())
                    else:
                        return (file_path, i + 1, line.rstrip())
    except:
        pass
    return None


def search_project_for_def(patterns, local_name, namespace=None):
    """Search the project for a definition, preferring files matching namespace."""
    try:
        # Use grep to find def declarations (abbrev is already reducible, doesn't need the attribute)
        result = subprocess.run(
            ['grep', '-rn', f'\\bdef {re.escape(local_name)}\\b', 'Mathlib/'],
            capture_output=True, text=True, timeout=60
        )

        candidates = []
        for line in result.stdout.split('\n'):
            if not line:
                continue
            parts = line.split(':', 2)
            if len(parts) >= 3:
                file_path = parts[0]
                line_num = int(parts[1])
                content = parts[2]

                for pattern in patterns:
                    if re.search(pattern, content):
                        candidates.append((file_path, line_num, content.rstrip()))
                        break

        if not candidates:
            return None

        # If namespace specified, prefer files that might contain that namespace
        if namespace:
            ns_parts = namespace.split('.')
            for file_path, line_num, content in candidates:
                # Check if file path suggests this namespace
                if any(part in file_path for part in ns_parts):
                    # Verify by searching file for namespace
                    verified = search_file_for_def(file_path, patterns, namespace)
                    if verified:
                        return verified

        # Fall back to first candidate
        return candidates[0] if candidates else None
    except:
        pass
    return None


def find_definition_after_line(file_path, attr_line):
    """Find the def that follows an attribute line.

    Only matches def declarations - abbrev is already reducible and doesn't need
    @[instance_reducible], and instance declarations don't need it either.
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()

        for i in range(attr_line - 1, min(len(lines), attr_line + 10)):
            line = lines[i]
            # Match def with any combination of protected/noncomputable modifiers
            if re.match(r'^\s*(protected\s+)?(noncomputable\s+)?def\s+\w+', line) or \
               re.match(r'^\s*noncomputable\s+protected\s+def\s+\w+', line):
                return (file_path, i + 1, line.rstrip())
    except:
        pass
    return None


def search_project_for_to_additive(additive_name):
    """
    Search entire project for @[to_additive ... additive_name ...].
    Returns (file_path, line_num, line_content) or None.
    """
    local_name = additive_name.rsplit('.', 1)[-1]
    try:
        result = subprocess.run(
            ['grep', '-rn', '-E', f'to_additive.*\\b{re.escape(local_name)}\\b', 'Mathlib/'],
            capture_output=True, text=True, timeout=60
        )

        for line in result.stdout.split('\n'):
            if not line:
                continue
            parts = line.split(':', 2)
            if len(parts) >= 3:
                file_path, line_num, content = parts[0], int(parts[1]), parts[2]
                # Find the definition that follows this attribute
                def_info = find_definition_after_line(file_path, line_num)
                if def_info:
                    return def_info
    except:
        pass
    return None


def already_has_instance_reducible(file_path, def_line):
    """Check if definition already has @[instance_reducible]."""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()

        # Check the definition line and preceding lines
        for i in range(max(0, def_line - 5), def_line):
            if 'instance_reducible' in lines[i]:
                return True
    except:
        pass
    return False


def add_instance_reducible(file_path, def_line, dry_run=False):
    """
    Add @[instance_reducible] to a definition.

    For @[to_additive ...], uses (attr := instance_reducible) syntax so the
    attribute applies to both the multiplicative and additive versions.

    Returns True if modification was made, False otherwise.
    """
    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    idx = def_line - 1  # Convert to 0-indexed

    if idx >= len(lines):
        return False

    line = lines[idx]

    # Find all attribute blocks preceding the definition
    # An attribute block starts with @[ and may span multiple lines until ]
    attr_blocks = []  # List of (start_idx, end_idx) tuples
    i = idx - 1
    while i >= 0 and i >= idx - 15:
        check_line = lines[i]
        stripped = check_line.strip()

        # Skip blank lines
        if not stripped:
            i -= 1
            continue

        # Skip line comments
        if stripped.startswith('--'):
            i -= 1
            continue

        # Check for attribute - either starts with @[ or ends with ] (multi-line attr end)
        if re.match(r'^\s*@\[', check_line):
            # Single or start of multi-line attribute
            end_idx = i
            bracket_count = check_line.count('[') - check_line.count(']')
            while bracket_count > 0 and end_idx < idx - 1:
                end_idx += 1
                bracket_count += lines[end_idx].count('[') - lines[end_idx].count(']')
            attr_blocks.append((i, end_idx))
            i -= 1
            continue

        # Check if this is the END of a multi-line attribute (ends with ])
        if stripped.endswith(']') and '-/' in check_line:
            # This looks like the end of a multi-line attribute with doc comment
            # Trace backward to find the @[ start
            start_idx = i
            bracket_count = check_line.count(']') - check_line.count('[')
            while bracket_count > 0 and start_idx > 0:
                start_idx -= 1
                bracket_count += lines[start_idx].count(']') - lines[start_idx].count('[')
            if '@[' in lines[start_idx]:
                attr_blocks.append((start_idx, i))
                i = start_idx - 1
                continue

        # Doc comments (standalone, not inside attribute)
        if stripped.startswith('/-'):
            i -= 1
            continue

        # Hit something else (like a previous definition) - stop looking
        break

    # Check if any attribute block contains to_additive
    for start_idx, end_idx in attr_blocks:
        attr_text = ''.join(lines[start_idx:end_idx + 1])
        if 'to_additive' in attr_text:
            # Special case: "to_additive existing" means additive version exists separately,
            # so we add instance_reducible as a separate attribute, not via (attr := ...)
            if 'to_additive existing' in attr_text or 'to_additive  existing' in attr_text:
                # Add instance_reducible at start of the attribute block
                new_line = re.sub(r'@\[', '@[instance_reducible, ', lines[start_idx], count=1)
                if not dry_run:
                    lines[start_idx] = new_line
                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.writelines(lines)
                return True

            # Normal to_additive: use (attr := instance_reducible) syntax
            for line_idx in range(start_idx, end_idx + 1):
                if 'to_additive' in lines[line_idx]:
                    new_line = re.sub(
                        r'to_additive(\s*)',
                        r'to_additive (attr := instance_reducible)\1',
                        lines[line_idx],
                        count=1
                    )
                    if new_line != lines[line_idx]:
                        # Check if line is too long (>100 chars) - if so, split at doc comment
                        if len(new_line.rstrip()) > 100:
                            # Try to split: @[to_additive (attr := ...) /-- doc -/]
                            # becomes: @[to_additive (attr := ...)\n  /-- doc -/]
                            match = re.match(
                                r'^(\s*@\[to_additive \(attr := instance_reducible\))(\s*)(/--)',
                                new_line
                            )
                            if match:
                                indent = re.match(r'^(\s*)', new_line).group(1)
                                new_line = match.group(1) + '\n' + indent + '  ' + new_line[match.end(2):]

                        if not dry_run:
                            lines[line_idx] = new_line
                            with open(file_path, 'w', encoding='utf-8') as f:
                                f.writelines(lines)
                        return True

    # No to_additive found - add instance_reducible to the first (closest) attribute block
    if attr_blocks:
        start_idx = attr_blocks[0][0]
        new_line = re.sub(r'@\[', '@[instance_reducible, ', lines[start_idx], count=1)
        if not dry_run:
            lines[start_idx] = new_line
            with open(file_path, 'w', encoding='utf-8') as f:
                f.writelines(lines)
        return True

    # Case: No existing attributes - add new line before definition
    indent = re.match(r'^(\s*)', line).group(1)
    new_attr_line = f'{indent}@[instance_reducible]\n'

    if not dry_run:
        lines.insert(idx, new_attr_line)
        with open(file_path, 'w', encoding='utf-8') as f:
            f.writelines(lines)

    return True


def file_to_module(file_path):
    """Convert file path to module name."""
    # Mathlib/Foo/Bar.lean -> Mathlib.Foo.Bar
    if file_path.endswith('.lean'):
        file_path = file_path[:-5]
    return file_path.replace('/', '.')


def verify_build(file_path, instance_name, timeout=300):
    """Build the module and check if warning is gone."""
    module = file_to_module(file_path)
    try:
        result = subprocess.run(
            ['lake', 'build', module],
            capture_output=True, text=True, timeout=timeout
        )
        output = result.stdout + result.stderr

        # Check if the specific warning is still present
        if f"instance `{instance_name}` must be marked" in output:
            return False, "Warning still present"

        # Success if our specific warning is gone (other errors may be pre-existing)
        return True, "OK"
    except subprocess.TimeoutExpired:
        return False, "Build timeout"
    except Exception as e:
        return False, str(e)


def main():
    args = parse_args()

    # Determine build target: --only takes precedence, then positional target
    build_target = args.only or args.target

    # Collect warnings
    output = run_build(build_target)
    warnings = parse_warnings(output, args)
    print(f"Found {len(warnings)} total instance_reducible warnings")

    # Filter by local/scoped
    warnings = filter_warnings(warnings, args)
    print(f"After filtering: {len(warnings)} warnings")

    # Filter by file if --only specified (not for positional target - that includes deps)
    if args.only:
        warnings = [w for w in warnings if w['file'] == args.only or w['file'].endswith('/' + args.only)]
        print(f"After --only {args.only}: {len(warnings)} warnings")

    # Limit to last N if specified
    if args.n is not None:
        warnings = warnings[-args.n:]
        print(f"Processing last {len(warnings)} warnings")

    # Deduplicate by instance name
    unique_warnings = deduplicate_by_instance(warnings)
    print(f"Unique instances to fix: {len(unique_warnings)}")
    print()

    # Group by definition file (not warning file - they may differ)
    by_def_file = defaultdict(list)
    not_found = []
    seen_def_locations = set()  # Track (file, line) to avoid duplicate fixes

    for w in unique_warnings:
        defn = find_definition(w['instance'], w['file'])
        if defn:
            def_file, def_line, def_content = defn
            # If --only specified, skip definitions in other files
            if args.only and def_file != args.only and not def_file.endswith('/' + args.only):
                not_found.append(w)
                continue

            # Skip if we've already seen this definition location
            # (e.g., both additive and multiplicative instances point to same def)
            def_loc = (def_file, def_line)
            if def_loc in seen_def_locations:
                continue
            seen_def_locations.add(def_loc)

            w['def_file'] = def_file
            w['def_line'] = def_line
            w['def_content'] = def_content
            by_def_file[def_file].append(w)
        else:
            not_found.append(w)

    print(f"Definitions found: {len(seen_def_locations)}")
    print(f"Definitions not found: {len(not_found)}")
    print()

    # Process files in reverse order (later files first to minimize rebuilds)
    file_order = sorted(by_def_file.keys(), reverse=True)

    success = []
    failed = []
    skipped = []

    for def_file in file_order:
        instances = by_def_file[def_file]
        print(f"\n{def_file} ({len(instances)} instance(s))")

        # Sort by line number descending within file
        instances.sort(key=lambda w: -w['def_line'])

        for w in instances:
            instance = w['instance']
            def_line = w['def_line']

            # Check if already fixed
            if already_has_instance_reducible(def_file, def_line):
                print(f"  SKIP: {instance} already has instance_reducible")
                skipped.append(w)
                continue

            if args.dry_run:
                print(f"  WOULD FIX: {instance} at line {def_line}")
                print(f"    {w['def_content'][:80]}")
                continue

            # Apply fix
            if add_instance_reducible(def_file, def_line):
                print(f"  FIXED: {instance} at line {def_line}")

                # Verify
                if not args.no_verify:
                    ok, msg = verify_build(def_file, instance)
                    if ok:
                        print(f"    ✓ Verified")
                        success.append(w)
                    else:
                        print(f"    ✗ Verification failed: {msg}")
                        failed.append(w)
                else:
                    success.append(w)
            else:
                print(f"  FAILED: Could not add attribute to {instance}")
                failed.append(w)

    # Summary
    print("\n" + "=" * 70)
    print("Summary")
    print("=" * 70)
    print(f"  Successful: {len(success)}")
    print(f"  Failed: {len(failed)}")
    print(f"  Skipped (already fixed): {len(skipped)}")
    print(f"  Definition not found: {len(not_found)}")

    if not_found:
        print("\nInstances needing manual review (definition not found):")
        for w in not_found[:10]:
            print(f"  - {w['instance']} (from {w['file']}:{w['line']})")
        if len(not_found) > 10:
            print(f"  ... and {len(not_found) - 10} more")

    if failed:
        print("\nFailed fixes:")
        for w in failed[:10]:
            print(f"  - {w['instance']} in {w.get('def_file', 'unknown')}")
        if len(failed) > 10:
            print(f"  ... and {len(failed) - 10} more")

    # Write logs
    log_dir = Path('/tmp/fix_instance_reducible')
    log_dir.mkdir(exist_ok=True)

    with open(log_dir / 'success.txt', 'w') as f:
        for w in success:
            f.write(f"{w['instance']}\t{w.get('def_file', '')}\t{w.get('def_line', '')}\n")

    with open(log_dir / 'failed.txt', 'w') as f:
        for w in failed + not_found:
            f.write(f"{w['instance']}\t{w['file']}:{w['line']}\n")

    print(f"\nLogs written to {log_dir}/")


if __name__ == '__main__':
    main()

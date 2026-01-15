import Mathlib.Tactic.UnsetOption

set_option linter.style.setOption false
set_option linter.unusedTactic false
set_option pp.all true

example : True := by
  run_tac
    let t ← Lean.pp.all.getM
    -- should be true as set
    guard (t == true)
  trivial

section

unset_option pp.all

example : True := by
  run_tac
    let t ← Lean.pp.all.getM
    -- should be default as unset
    guard (t == false)
  trivial

end

example : True := by
  run_tac
    let t ← Lean.pp.all.getM
    -- should be true as only unset within section
    guard (t == true)
  trivial

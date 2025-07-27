/-
Copyright (c) 2025 Matej Penciak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matej Penciak
-/
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.Topology.Defs.Filter

/-!
# Quasi-finite morphisms

A morphism of schemes `f : X ⟶ Y` is quasi-finite if every point in every fiber is isolated
in its fiber. In other words, for every point `x : X`, the point `x` viewed as a point in the
fiber `f.fiber (f.base x)` has a trivial punctured neighborhood filter.

-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry Topology

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism `f : X ⟶ Y` is quasi-finite if every point in every fiber is isolated
in its fiber. -/
@[mk_iff]
class QuasiFinite (f : X ⟶ Y) : Prop where
  /-- Every point in every fiber is isolated in its fiber -/
  isolated_in_fiber : ∀ x : X, 𝓝[≠] (f.asFiber x) = ⊥

-- Basic lemma to check that our definition is working
lemma quasiFinite_iff_isolated_fibers (f : X ⟶ Y) :
    QuasiFinite f ↔ ∀ x : X, 𝓝[≠] (f.asFiber x) = ⊥ := by
  exact quasiFinite_iff f

end AlgebraicGeometry

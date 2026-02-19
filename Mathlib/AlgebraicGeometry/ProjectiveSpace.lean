/-
Copyright (c) 2026 Matej Penciak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matej Penciak
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective space

## Main definitions
- `AlgebraicGeometry.ProjectiveSpace`:
-/

@[expose] public section

open CategoryTheory Limits MvPolynomial

noncomputable section

namespace AlgebraicGeometry

universe v u

variable (n : Type v) (S : Scheme.{max u v})

local notation3 "ℤ[" n "]" => CommRingCat.of (MvPolynomial n (ULift ℤ))
local notation3 "ℤ[" n "].{" u ", " v "}" => CommRingCat.of (MvPolynomial n (ULift.{max u v} ℤ))

#check MvPolynomial.gradedAlgebra
#check homogeneousSubmodule

def ProjectiveSpace (n : Type v) (S : Scheme.{max u v}) : Scheme.{max u v} :=
  haveI := @MvPolynomial.gradedAlgebra n (ULift.{max u v} ℤ)
  pullback (terminal.from S) (terminal.from (Proj ℤ[n].{u, v}))

namespace ProjectiveSpace

scoped[AlgebraicGeometry] notation "ℙ(" n ";" S ")" => ProjectiveSpace n S

end ProjectiveSpace

end AlgebraicGeometry

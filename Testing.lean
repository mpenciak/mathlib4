import Mathlib

open BigOperators DirectSum

noncomputable section

example {σ R} [CommSemiring R] :
    MvPolynomial σ R ≃ₐ[R] ⨁ i, MvPolynomial.homogeneousSubmodule σ R i where
      toFun := MvPolynomial.decompose' _ 1
      invFun := DirectSum.toModule _ _ _ fun n => (MvPolynomial.homogeneousSubmodule σ R n).subtype
      left_inv := sorry
      right_inv := sorry
      map_mul' := sorry
      map_add' := sorry
      commutes' := sorry

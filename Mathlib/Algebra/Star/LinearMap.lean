/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.WithConv
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Intrinsic star operation on linear maps

This file defines the star operation on linear maps: `(star f) x = star (f (star x))`.
This corresponds to a map being star-preserving, i.e., a map is self-adjoint iff it
is star-preserving.

## Implementation notes

Because there is a global `star` instance on `H →ₗ[𝕜] H` (defined as the linear map adjoint on
finite-dimensional Hilbert spaces), which is mathematically distinct from this `star`, we provide
this instance on `WithConv (E →ₗ[R] F)`.

The reason we chose `WithConv` is because together with the convolution product from
`Mathlib/RingTheory/Coalgebra/Convolution.lean`, we get a ⋆-algebra when
`star (WithConv.toConv comul) = WithConv.toConv (comm ∘ comul)`. -/

@[expose] public section

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

open WithConv

namespace LinearMap

/-- The intrinsic star operation on linear maps `E →ₗ F` defined by
`(star f) x = star (f (star x))`. -/
@[instance_reducible]
def intrinsicStar : Star (E →ₗ[R] F) where
  star f :=
  { toFun x := star (f (star x))
    map_add' := by simp
    map_smul' := by simp }

@[simp] theorem intrinsicStar_apply (f : WithConv (E →ₗ[R] F)) (x : E) :
    (star f) x = star (f (star x)) := rfl

/-- The involutive intrinsic star structure on linear maps. -/
@[instance_reducible] def intrinsicInvolutiveStar : InvolutiveStar (E →ₗ[R] F) where
  star_involutive x := by ext; simp

/-- The intrinsic star additive monoid structure on linear maps. -/
@[instance_reducible]
def intrinsicStarAddMonoid : StarAddMonoid (E →ₗ[R] F) where
  star_add x y := by ext; simp

/-- A linear map is self-adjoint (with respect to the intrinsic star) iff it is star-preserving. -/
theorem IntrinsicStar.isSelfAdjoint_iff_map_star (f : WithConv (E →ₗ[R] F)) :
    IsSelfAdjoint f ↔ ∀ x, f (star x) = star (f x) := by
  simp_rw [IsSelfAdjoint, WithConv.ext_iff, LinearMap.ext_iff, intrinsicStar_apply,
   star_eq_iff_star_eq, eq_comm]

@[deprecated (since := "2025-12-09")]
alias isSelfAdjoint_iff_map_star := IntrinsicStar.isSelfAdjoint_iff_map_star

/-- A star-preserving linear map is self-adjoint (with respect to the intrinsic star). -/
@[simp]
protected theorem _root_.IntrinsicStar.StarHomClass.isSelfAdjoint {S : Type*} [FunLike S E F]
    [LinearMapClass S R E F] [StarHomClass S E F] {f : S} :
    IsSelfAdjoint (toConv (f : E →ₗ[R] F) : WithConv (E →ₗ[R] F)) :=
  IntrinsicStar.isSelfAdjoint_iff_map_star _ |>.mpr (map_star f)

@[deprecated (since := "2025-12-09")]
alias _root_.StarHomClass.isSelfAdjoint := _root_.IntrinsicStar.StarHomClass.isSelfAdjoint

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]

theorem intrinsicStar_comp (f : WithConv (E →ₗ[R] F)) (g : WithConv (G →ₗ[R] E)) :
    star (toConv (f.ofConv ∘ₗ g.ofConv)) = toConv ((star f).ofConv ∘ₗ (star g).ofConv) := by
  ext; simp

@[simp] theorem intrinsicStar_id :
    star (toConv (LinearMap.id (R := R) (M := E))) = toConv LinearMap.id := by ext; simp
theorem intrinsicStar_zero : star (0 : WithConv (E →ₗ[R] F)) = 0 := by simp

section NonUnitalNonAssocSemiring
variable {R' E : Type*} [CommSemiring R'] [StarRing R']
  [NonUnitalNonAssocSemiring E] [StarRing E] [Module R E] [Module R' E]
  [StarModule R E] [StarModule R' E] [SMulCommClass R E E] [IsScalarTower R E E]

theorem intrinsicStar_mulLeft (x : E) :
    star (toConv (mulLeft R x)) = toConv (mulRight R (star x)) := by ext; simp

theorem intrinsicStar_mulRight (x : E) :
    star (toConv (mulRight R x)) = toConv (mulLeft R (star x)) := by
  rw [star_eq_iff_star_eq, intrinsicStar_mulLeft, star_star]

theorem intrinsicStar_mul' [SMulCommClass R' E E] [IsScalarTower R' E E] :
    star (toConv (mul' R' E)) = toConv (mul' R' E ∘ₗ TensorProduct.comm R' E E) :=
  WithConv.ext <| TensorProduct.ext' fun _ _ ↦ by simp

end NonUnitalNonAssocSemiring

variable [SMulCommClass R R F] in
instance intrinsicStarModule : StarModule R (WithConv (E →ₗ[R] F)) where
  star_smul _ _ := by ext; simp

section CommSemiring
variable {R E F G H : Type*} [CommSemiring R] [StarRing R]
  [AddCommMonoid E] [StarAddMonoid E] [Module R E] [StarModule R E]
  [AddCommMonoid F] [StarAddMonoid F] [Module R F] [StarModule R F]
  [AddCommMonoid G] [StarAddMonoid G] [Module R G] [StarModule R G]
  [AddCommMonoid H] [StarAddMonoid H] [Module R H] [StarModule R H]

theorem _root_.TensorProduct.intrinsicStar_map
    (f : WithConv (E →ₗ[R] F)) (g : WithConv (G →ₗ[R] H)) :
    star (toConv (TensorProduct.map f.ofConv g.ofConv)) =
      toConv (TensorProduct.map (star f).ofConv (star g).ofConv) :=
  WithConv.ext <| TensorProduct.ext' fun _ _ ↦ by simp

theorem intrinsicStar_lTensor (f : WithConv (F →ₗ[R] G)) :
    star (toConv (lTensor E f.ofConv)) = toConv (lTensor E (star f).ofConv) := by ext; simp

theorem intrinsicStar_rTensor (f : WithConv (E →ₗ[R] F)) :
    star (toConv (rTensor G f.ofConv)) = toConv (rTensor G (star f).ofConv) := by ext; simp

theorem intrinsicStar_eq_comp (f : WithConv (E →ₗ[R] F)) :
    star f =
      toConv ((starLinearEquiv R).toLinearMap ∘ₛₗ f.ofConv ∘ₛₗ (starLinearEquiv R).toLinearMap) :=
  rfl

theorem IntrinsicStar.starLinearEquiv_eq_arrowCongr :
    starLinearEquiv R (A := WithConv (E →ₗ[R] F)) =
      (WithConv.linearEquiv R _).trans
      (((starLinearEquiv R).arrowCongr (starLinearEquiv R)).trans
        (WithConv.linearEquiv R _).symm) := rfl

end CommSemiring

section starAddMonoidSemiring
variable {S : Type*} [Semiring S] [StarAddMonoid S] [StarModule S S] [Module S E] [StarModule S E]

@[simp] theorem intrinsicStar_toSpanSingleton (a : E) :
    star (toConv (toSpanSingleton S E a)) = toConv (toSpanSingleton S E (star a)) := by ext; simp

theorem intrinsicStar_smulRight [Module S F] [StarModule S F] (f : WithConv (E →ₗ[S] S)) (x : F) :
    star (toConv (f.ofConv.smulRight x)) = toConv ((star f).ofConv.smulRight (star x)) := by
  ext; simp

end starAddMonoidSemiring

end LinearMap

section matrix
variable {R m n : Type*} [CommSemiring R] [StarRing R] [Fintype m] [DecidableEq m]

namespace LinearMap

theorem toMatrix'_intrinsicStar (f : WithConv ((m → R) →ₗ[R] (n → R))) :
    (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star := by
  ext; simp

/-- A linear map `f : (m → R) →ₗ (n → R)` is self-adjoint (with respect to the intrinsic star)
iff its corresponding matrix `f.toMatrix'` has all self-adjoint elements.
So star-preserving maps correspond to their matrices containing only self-adjoint elements. -/
theorem IntrinsicStar.isSelfAdjoint_iff_toMatrix' (f : WithConv ((m → R) →ₗ[R] (n → R))) :
    IsSelfAdjoint f ↔ ∀ i j, IsSelfAdjoint (f.ofConv.toMatrix' i j) := by
  simp [IsSelfAdjoint, ← toMatrix'.injective.eq_iff, toMatrix'_intrinsicStar, ← Matrix.ext_iff,
    WithConv.ext_iff]

end LinearMap

namespace Matrix

theorem intrinsicStar_toLin' (A : Matrix n m R) :
    star (toConv A.toLin') = toConv (A.map star).toLin' := by
  simp [← LinearMap.toMatrix'.injective.eq_iff, LinearMap.toMatrix'_intrinsicStar, WithConv.ext_iff]

/-- Given a matrix `A`, `A.toLin'` is self-adjoint (with respect to the intrinsic star)
iff all its elements are self-adjoint. -/
theorem IntrinsicStar.isSelfAdjoint_toLin'_iff (A : Matrix n m R) :
    IsSelfAdjoint (toConv A.toLin') ↔ ∀ i j, IsSelfAdjoint (A i j) := by
  simp [IsSelfAdjoint, intrinsicStar_toLin', ← ext_iff]

end Matrix
end matrix

namespace Module.End

/-- Intrinsic star operation for `(End R E)ˣ`. -/
@[instance_reducible]
def Units.intrinsicStar : Star (End R E)ˣ where
  star f := by
    refine ⟨star f, star (f⁻¹ : (End R E)ˣ), ?_, ?_⟩
    all_goals
      ext
      simp only [mul_apply, LinearMap.intrinsicStar_apply, star_star]
      rw [← LinearMap.comp_apply]
      simp [← mul_eq_comp, one_eq_id]

theorem IsUnit.intrinsicStar {f : WithConv (End R E)} (hf : IsUnit f.ofConv) :
    IsUnit (star f).ofConv := by
  have ⟨u, hu⟩ := hf
  have : IsUnit (star (toConv (u : End R E))).ofConv := (star (toConv u)).ofConv.isUnit
  simpa [hu] using this

open Module.End in
@[simp] theorem isUnit_intrinsicStar_iff {f : WithConv (End R E)} :
    IsUnit (star f).ofConv ↔ IsUnit f.ofConv :=
  ⟨fun h ↦ star_star f ▸ h.intrinsicStar, fun h ↦ h.intrinsicStar⟩

section eigenspace
variable {R V : Type*} [CommRing R] [InvolutiveStar R] [AddCommGroup V] [StarAddMonoid V]
  [Module R V] [StarModule R V]

open LinearMap

theorem mem_eigenspace_intrinsicStar_iff (f : WithConv (End R V)) (α : R) (x : V) :
    x ∈ (star f).ofConv.eigenspace α ↔ star x ∈ f.ofConv.eigenspace (star α) := by
  simp_rw [mem_eigenspace_iff, intrinsicStar_apply, star_eq_iff_star_eq, star_smul, eq_comm]

@[simp]
theorem spectrum_intrinsicStar (f : WithConv (End R V)) :
    spectrum R (star f).ofConv = star (spectrum R f.ofConv) := by
  ext x
  simp_rw [Set.mem_star, spectrum.mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one]
  rw [← isUnit_intrinsicStar_iff]
  simp [one_eq_id]

end eigenspace
end Module.End

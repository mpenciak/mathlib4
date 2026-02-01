/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Grassmannians

## Main definitions

- `Module.Grassmannian`: `G(k, M; R)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined
  to be the set of submodules of `M` whose **quotient** is locally free of rank `k`. Note that there
  is another convention in literature where the `k`ᵗʰ Grassmannian would instead be `k`-dimensional
  subspaces of a given vector space over a field. See implementation notes below.

- `Module.Grassmannian.functor`: The Grassmannian functor that sends an `R`-algebra `A` to the set
  `G(k, A ⊗[R] M; A)`.

## Implementation notes

In the literature, two conventions exist:

1. The `k`ᵗʰ Grassmannian parametrises `k`-dimensional **subspaces** of a given finite-dimensional
   vector space over a field.
2. The `k`ᵗʰ Grassmannian parametrises **quotients** that are locally free of rank `k`, of a given
   module over a ring.

For the purposes of Algebraic Geometry, the first definition here cannot be generalised to obtain
a scheme to represent the functor, which is why the second definition is the one chosen by
[Grothendieck, EGA I.9.7.3][grothendieck-1971] (Springer edition only), and in EGA V.11
(unpublished).

The first definition in the stated generality (i.e. over a field `F`, and finite-dimensional vector
space `V`) can be recovered from the second definition by noting that `k`-dimensional subspaces of
`V` are canonically equivalent to `(n-k)`-dimensional quotients of `V`, and also to `k`-dimensional
quotients of `V*`, the dual of `V`. In symbols, this means that the first definition is equivalent
to `G(n - k, V; F)` and also to `G(k, V →ₗ[F] F; F)`, where `n` is the dimension of `V`.

## TODO
- Define and recover the subspace-definition (i.e. the first definition above).
- Define `chart x` indexed by `x : Fin k → M` as a subtype consisting of those
  `N ∈ G(k, A ⊗[R] M; A)` such that the composition `R^k → M → M⧸N` is an isomorphism.
- Define `chartFunctor x` to turn `chart x` into a subfunctor of `Module.Grassmannian.functor`. This
  will correspond to an affine open chart in the Grassmannian.
- Grassmannians for schemes and quasi-coherent sheaf of modules.
- Representability of `Module.Grassmannian.functor R M k`.
-/

@[expose] public section

universe u v w

namespace Module

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (k : ℕ)

/-- `G(k, M; R)` is the `k`ᵗʰ Grassmannian of the `R`-module `M`. It is defined to be the set of
submodules of `M` whose quotient is locally free of rank `k`. Note that there is another convention
in literature where instead the submodule is required to have rank `k`. See the module docstring
of `RingTheory.Grassmannian`. -/
@[stacks 089R] structure Grassmannian extends Submodule R M where
  finite_quotient : Module.Finite R (M ⧸ toSubmodule)
  projective_quotient : Projective R (M ⧸ toSubmodule)
  rankAtStalk_eq : ∀ p, rankAtStalk (R := R) (M ⧸ toSubmodule) p = k

attribute [instance] Grassmannian.finite_quotient Grassmannian.projective_quotient

namespace Grassmannian

@[inherit_doc] scoped notation "G(" k ", " M "; " R ")" => Grassmannian R M k

variable {R M k}

instance : CoeOut G(k, M; R) (Submodule R M) :=
  ⟨toSubmodule⟩

@[ext] lemma ext {N₁ N₂ : G(k, M; R)} (h : (N₁ : Submodule R M) = N₂) : N₁ = N₂ := by
  cases N₁; cases N₂; congr 1

section Functor

open CategoryTheory TensorProduct AlgebraTensorModule

variable (A : Type w) [CommRing A] [Algebra R A]
variable (B : Type w) [CommRing B] [Algebra R B]
variable [Algebra A B] [IsScalarTower R A B]

lemma cancelBaseChange_eq_lid :
    cancelBaseChange R A A A M = TensorProduct.lid A (A ⊗[R] M) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp only [cancelBaseChange_tmul, lid_tmul, smul_tmul', smul_eq_mul, mul_comm]
    | add x y hx hy =>
      simp only [tmul_add, map_add, lid_tmul, hx, hy]
  | add x y hx hy => simp [hx, hy]

lemma baseChange_mkQ_surjective (N : G(k, (A ⊗[R] M); A)) :
    Function.Surjective
      ((Submodule.mkQ N.toSubmodule).baseChange B ∘ₗ
        (cancelBaseChange R A B B M).symm.toLinearMap) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul b q =>
    obtain ⟨a_m, rfl⟩ := Submodule.Quotient.mk_surjective N.toSubmodule q
    exact ⟨(cancelBaseChange R A B B M) (b ⊗ₜ[A] a_m), by simp⟩
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy']⟩

/-- The map on Grassmannians induced by base change along an algebra map `A → B`.
Given a submodule `N` of `A ⊗[R] M`, the image is the kernel of the composition
`B ⊗[R] M ≃ B ⊗[A] (A ⊗[R] M) → B ⊗[A] ((A ⊗[R] M) ⧸ N)`. -/
def map (N : G(k, (A ⊗[R] M); A)) : G(k, (B ⊗[R] M); B) where
  toSubmodule :=
    let f := (Submodule.mkQ N.toSubmodule).baseChange B ∘ₗ
      (cancelBaseChange R A B B M).symm.toLinearMap
    f.ker
  finite_quotient := by
    let f := (Submodule.mkQ N.toSubmodule).baseChange B ∘ₗ
             (cancelBaseChange R A B B M).symm.toLinearMap
    have equiv := f.quotKerEquivOfSurjective (baseChange_mkQ_surjective A B N)
    exact Module.Finite.equiv equiv.symm
  projective_quotient := by
    let f := (Submodule.mkQ N.toSubmodule).baseChange B ∘ₗ
               (cancelBaseChange R A B B M).symm.toLinearMap
    have equiv := f.quotKerEquivOfSurjective (baseChange_mkQ_surjective A B N)
    exact Module.Projective.of_equiv equiv.symm
  rankAtStalk_eq := by
    intro p
    let f := (Submodule.mkQ N.toSubmodule).baseChange B ∘ₗ
             (cancelBaseChange R A B B M).symm.toLinearMap
    have equiv := f.quotKerEquivOfSurjective (baseChange_mkQ_surjective A B N)
    have hEquiv := Module.rankAtStalk_eq_of_equiv (R:=B)
        (M:= (B ⊗[R] M ⧸ f.ker))
        (N:= B ⊗[A] ((A ⊗[R] M) ⧸ N.toSubmodule)) equiv
    have h1 : rankAtStalk (R:=B) (B ⊗[R] M ⧸ f.ker) p =
        rankAtStalk (R:=B) (B ⊗[A] ((A ⊗[R] M) ⧸ N.toSubmodule)) p := by
      simpa using congrArg (fun g => g p) hEquiv
    have h2 := Module.rankAtStalk_baseChange (R:=A)
      (M:= (A ⊗[R] M ⧸ N.toSubmodule)) (S:=B) (p:=p)
    calc
      rankAtStalk (R:=B) (B ⊗[R] M ⧸ f.ker) p
          = rankAtStalk (R:=B) (B ⊗[A] ((A ⊗[R] M) ⧸ N.toSubmodule)) p := h1
      _ = rankAtStalk (R:=A) ((A ⊗[R] M ⧸ N.toSubmodule))
        (PrimeSpectrum.comap (algebraMap A B) p) := by
        simpa using h2
      _ = k := N.rankAtStalk_eq _

variable (R M k)

/-- The Grassmannian functor sends an `R`-algebra `A` to `G(k, A ⊗[R] M; A)`. -/
def functor : CommAlgCat.{w, u} R ⥤ Type (max v w) where
  obj A := G(k, (A ⊗[R] M); A)
  map {A B} f := by
    letI : Algebra A B := f.hom.toAlgebra
    haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' (by
      ext r; simp only [RingHom.comp_apply]; exact (f.hom.commutes r).symm)
    exact map A B
  map_id := by
    intro A
    ext1 N
    simp only [CommAlgCat.hom_id, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom, types_id_apply]
    ext x
    simp only [map, cancelBaseChange_eq_lid, LinearMap.mem_ker, LinearMap.coe_comp,
               LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.lid_symm_apply,
               LinearMap.baseChange_tmul, Submodule.mkQ_apply]
    rw [← (TensorProduct.lid A ((A ⊗[R] M) ⧸ N.toSubmodule)).injective.eq_iff]
    simp only [TensorProduct.lid_tmul, map_zero, one_smul, Submodule.Quotient.mk_eq_zero]
  map_comp := by
    intro A B C f g
    letI : Algebra A B := f.hom.toAlgebra
    letI : Algebra B C := g.hom.toAlgebra
    letI : Algebra A C := (g.hom.comp f.hom).toAlgebra
    haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' (by
      ext r; simp only [RingHom.comp_apply]; exact (f.hom.commutes r).symm)
    haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' (by
      ext r; simp only [RingHom.comp_apply]; exact (g.hom.commutes r).symm)
    haveI : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' (by
      ext r; exact (g.hom.comp f.hom).commutes r |>.symm)
    haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' (by
      ext a
      change ((g.hom.comp f.hom) a) = g.hom (f.hom a)
      simp [AlgHom.comp_apply])
    ext1 N
    ext x
    let Q : Type (max v w) := (A ⊗[R] M) ⧸ N.toSubmodule
    let fAB : B ⊗[R] M →ₗ[B] B ⊗[A] Q :=
      (Submodule.mkQ N.toSubmodule).baseChange B ∘ₗ
        (cancelBaseChange R A B B M).symm.toLinearMap
    let eAB := fAB.quotKerEquivOfSurjective (baseChange_mkQ_surjective A B N)
    let eAB_C :=
      LinearEquiv.baseChange (R:=B) (A:=C) (M:= (B ⊗[R] M ⧸ fAB.ker)) (N:= B ⊗[A] Q) eAB
    let eAssoc := cancelBaseChange A B C C Q
    let e := eAB_C.trans eAssoc
    let fAC : C ⊗[R] M →ₗ[C] C ⊗[A] Q :=
      (Submodule.mkQ N.toSubmodule).baseChange C ∘ₗ
        (cancelBaseChange R A C C M).symm.toLinearMap
    let fBC : C ⊗[R] M →ₗ[C] C ⊗[B] (B ⊗[R] M ⧸ fAB.ker) :=
      (Submodule.mkQ (LinearMap.ker fAB)).baseChange C ∘ₗ
        (cancelBaseChange R B C C M).symm.toLinearMap
    have hcomp : (e.toLinearMap.comp fBC) = fAC := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp [fAC, fBC, e, eAssoc, eAB_C, eAB, fAB, Q]
      | tmul c m =>
        simp [fAC, fBC, e, eAssoc, eAB_C, eAB, fAB, Q,
          LinearMap.baseChange_tmul, cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul,
          cancelBaseChange_tmul, LinearMap.quotKerEquivOfSurjective_apply_mk]
      | add x y hx hy =>
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_add] at hx hy ⊢
        rw [hx, hy]
    have hker : fAC.ker = fBC.ker := hcomp ▸ LinearEquiv.ker_comp e fBC
    simp [map, fAB, fAC, fBC, hker]

end Functor

end Grassmannian

end Module

/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Subfunctor.Basic
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

TODO: turn these TODOs into an actual description of what's done

- Define `chart x` indexed by `x : Fin k → M` as a subtype consisting of those
  `N ∈ G(k, A ⊗[R] M; A)` such that the composition `R^k → M → M⧸N` is an isomorphism.
- Define `chartFunctor x` to turn `chart x` into a subfunctor of `Module.Grassmannian.functor`. This
  will correspond to an affine open chart in the Grassmannian.

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

lemma baseChange_mkQ_surjective (N : G(k, A ⊗[R] M; A)) :
    Function.Surjective (N.toSubmodule.mkQ.baseChange B ∘ₗ
      (cancelBaseChange R A B B M).symm.toLinearMap) := by
  apply ((cancelBaseChange R A B B M).symm.surjective_comp (LinearMap.baseChange B N.mkQ)).mpr
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective _ <| Submodule.mkQ_surjective N.toSubmodule

/-- The map on Grassmannians induced by base change along an algebra map `A → B`.
Given a submodule `N` of `A ⊗[R] M`, the image is the kernel of the composition
`B ⊗[R] M ≃ B ⊗[A] (A ⊗[R] M) → B ⊗[A] ((A ⊗[R] M) ⧸ N)`. -/
def map (N : G(k, A ⊗[R] M; A)) : G(k, B ⊗[R] M; B) :=
  letI f := N.toSubmodule.mkQ.baseChange B ∘ₗ (cancelBaseChange R A B B M).symm.toLinearMap
  haveI equiv := f.quotKerEquivOfSurjective (baseChange_mkQ_surjective A B N)
  { toSubmodule := f.ker
    finite_quotient := Module.Finite.equiv equiv.symm
    projective_quotient := Module.Projective.of_equiv equiv.symm
    rankAtStalk_eq p := by
      calc
        _ = rankAtStalk (R := B) (B ⊗[A] ((A ⊗[R] M) ⧸ N.toSubmodule)) p := by
          simpa using congrArg (fun g => g p) <| Module.rankAtStalk_eq_of_equiv equiv
        _ = rankAtStalk (R := A) (A ⊗[R] M ⧸ N.toSubmodule)
            (PrimeSpectrum.comap (algebraMap A B) p) := by
          simpa using Module.rankAtStalk_baseChange ..
        _ = k := N.rankAtStalk_eq _ }

variable (R M k)

theorem map_id (A : CommAlgCat R) : map A A = 𝟙 G(k, A ⊗[R] M; A)  := by
    ext1 N
    rw [types_id_apply]
    ext x
    simp only [map, cancelBaseChange_self_eq_lid, LinearMap.mem_ker, LinearMap.coe_comp,
               LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.lid_symm_apply,
               LinearMap.baseChange_tmul, Submodule.mkQ_apply]
    rw [← (TensorProduct.lid A ((A ⊗[R] M) ⧸ N.toSubmodule)).injective.eq_iff]
    simp only [TensorProduct.lid_tmul, map_zero, one_smul, Submodule.Quotient.mk_eq_zero]

theorem map_comp {A B C : CommAlgCat R}
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower R A B] [IsScalarTower R B C] [IsScalarTower R A C]
    [IsScalarTower A B C] (N : G(k, A ⊗[R] M; A)) :
    map A C N = map B C (map A B N) := by
    ext x
    let fAB := N.toSubmodule.mkQ.baseChange B ∘ₗ (cancelBaseChange _ _ _ _ _).symm.toLinearMap
    let fAC := N.toSubmodule.mkQ.baseChange C ∘ₗ (cancelBaseChange _ _ _ _ _).symm.toLinearMap
    let fBC := fAB.ker.mkQ.baseChange C ∘ₗ (cancelBaseChange _ _ _ _ _).symm.toLinearMap
    let e := (fAB.quotKerEquivOfSurjective (baseChange_mkQ_surjective _ _ _)).baseChange _ _
        ≪≫ₗ cancelBaseChange _ _ _ C _
    have hcomp : e.toLinearMap.comp fBC = fAC := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp [fAC, fBC, e]
      | tmul c m =>
        simp [fAB, fAC, fBC, e, LinearMap.baseChange_tmul, cancelBaseChange_symm_tmul,
          LinearEquiv.baseChange_tmul, cancelBaseChange_tmul,
          LinearMap.quotKerEquivOfSurjective_apply_mk]
      | add x y hx hy =>
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_add] at *
        rw [hx, hy]
    simp [map, fAB, fAC, fBC, hcomp ▸ LinearEquiv.ker_comp e fBC]

/-- The Grassmannian functor sends an `R`-algebra `A` to `G(k, A ⊗[R] M; A)`. -/
def functor : CommAlgCat.{w, u} R ⥤ Type (max v w) where
  obj A := G(k, A ⊗[R] M; A)
  map {A B} f := by
    letI : Algebra A B := f.hom.toAlgebra
    haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' (by
      ext r; simp only [RingHom.comp_apply]; exact (f.hom.commutes r).symm)
    exact map A B
  map_id A := map_id R M k A
  map_comp {A B C} f g  := by
    algebraize [f.hom.toRingHom, g.hom.toRingHom, (f ≫ g).hom.toRingHom]
    haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' (by
      ext a
      change ((g.hom.comp f.hom) a) = g.hom (f.hom a)
      simp [AlgHom.comp_apply])
    exact funext (map_comp R M k)

end Functor

section Chart

variable (k : ℕ) (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

open CategoryTheory TensorProduct

def chart (x : Fin k → M) :=
  { N : G(k, M; R) // Function.Bijective <| N.mkQ ∘ₗ Fintype.linearCombination R x }

variable (A : Type w) [CommRing A] [Algebra R A]
variable (B : Type w) [CommRing B] [Algebra R B]
variable [Algebra A B] [IsScalarTower R A B]

def asdf (x : Fin k → M) : (Fin k → A) →ₗ[A] A ⊗[R] M := by
  let tt := (Fintype.linearCombination R x).baseChange A
  let dd : (Fin k → A) ≃ₗ[A] A ⊗[R] (Fin k → R) := (piScalarRight R A A (Fin k)).symm
  exact tt ∘ₗ dd

/-- The chart condition is preserved under base change: if the chart map
for `N` over `A` is bijective, then it is also bijective for
`map A B N` over `B`. The proof factors the map over `B` as a
composition of three bijections:
1. `(piScalarRight A B B).symm`
2. base change of the original iso from `hN`
3. `quotKerEquivOfSurjective.symm` -/
lemma map_chart_bijective (x : Fin k → M)
    (N : G(k, A ⊗[R] M; A)) (hN : Function.Bijective (N.mkQ ∘ₗ asdf k R M A x)) :
    Function.Bijective ((map A B N).mkQ ∘ₗ asdf k R M B x) := by
  open TensorProduct AlgebraTensorModule in
  -- The surjective map whose kernel defines map A B N
  let g := N.toSubmodule.mkQ.baseChange B ∘ₗ (cancelBaseChange R A B B M).symm.toLinearMap
  have hg_surj : Function.Surjective g :=
    baseChange_mkQ_surjective A B N
  -- Build the composed equivalence
  let e := LinearEquiv.ofBijective (N.mkQ ∘ₗ asdf k R M A x) hN
  let eB := LinearEquiv.baseChange A B _ _ e
  let totalEquiv : (Fin k → B) ≃ₗ[B] (B ⊗[R] M ⧸ (map A B N).toSubmodule) :=
    (piScalarRight A B B (Fin k)).symm ≪≫ₗ eB ≪≫ₗ
      (g.quotKerEquivOfSurjective hg_surj).symm
  -- It suffices to show this equiv agrees with the goal map
  suffices h : ⇑totalEquiv = ⇑((map A B N).mkQ ∘ₗ asdf k R M B x) from
    h ▸ totalEquiv.bijective
  -- Both sides send v : Fin k → B to mkQ(∑ᵢ v(i) ⊗ x(i)).
  -- This boils down to: quotKerEquiv.symm (g z) = mkQ z, and a naturality
  -- / compatibility statement between the various base change constructions.'
  funext v
  -- Unfold the LHS: totalEquiv v = quotEquiv.symm (eB (piScalarRight.symm v))
  -- Unfold the RHS: (map A B N).mkQ (asdf B x v) = g.ker.mkQ (asdf B x v)
  -- These are equal because:
  -- (a) quotEquiv.symm (g z) = g.ker.mkQ z
  --     (by quotKerEquivOfSurjective_symm_apply)
  -- (b) eB (piScalarRight A B B .symm v) = g (asdf B x v)
  --     The base-changed iso composed with piScalarRight
  --     equals g ∘ asdf. This follows from:
  --     - baseChange_baseChange naturality
  --     - lTensor_comp: baseChange preserves composition
  --     - piScalarRight compatibility with cancelBaseChange
  -- The LHS unfolds to quotEquiv.symm (eB (piScalarRight.symm v))
  -- The RHS unfolds to g.ker.mkQ (asdf B x v)
  -- Step: show eB (piScalarRight.symm v) = g (asdf B x v), then use quotKerEquiv_symm_apply
  change (g.quotKerEquivOfSurjective hg_surj).symm
      (eB ((piScalarRight A B B (Fin k)).symm v)) =
    (map A B N).toSubmodule.mkQ (asdf k R M B x v)
  suffices key : eB ((piScalarRight A B B (Fin k)).symm v) = g (asdf k R M B x v) by
    rw [key, LinearMap.quotKerEquivOfSurjective_symm_apply]; rfl
  -- Prove: eB (piScalarRight.symm v) = g (asdf B x v)
  -- Both sides are B-linear in v, so it suffices to check on Pi.single j 1.
  -- Both sides then evaluate to 1 ⊗ N.mkQ(1 ⊗ x(j)) in B ⊗[A] (quotient).
  suffices hgen : ∀ j : Fin k,
      eB ((piScalarRight A B B (Fin k)).symm (Pi.single j (1 : B))) =
      g (asdf k R M B x (Pi.single j 1)) by
    -- Extend from generators to all v by linearity
    have hv : v = ∑ j : Fin k, v j • Pi.single j 1 := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    conv_rhs => rw [hv]
    simp only [map_sum, map_smul, hgen]
  -- Check on each standard basis element
  intro j
  simp only [piScalarRight_symm_single, eB, e, LinearEquiv.baseChange_tmul,
    LinearEquiv.ofBijective_apply, LinearMap.comp_apply]
  -- LHS is now: 1 ⊗ N.mkQ (asdf A x (Pi.single j 1))
  -- RHS needs: g (asdf B x (Pi.single j 1))
  -- Unfold asdf on both sides: asdf S x (Pi.single j 1) = 1 ⊗ x j
  unfold asdf
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, piScalarRight_symm_single,
    LinearMap.baseChange_tmul, Fintype.linearCombination_apply_single, one_smul]
  -- Now LHS: 1 ⊗ N.mkQ (1 ⊗ x j)
  -- RHS: g (1 ⊗ x j) = N.mkQ.baseChange B (cancelBaseChange.symm (1 ⊗ x j))
  --     = N.mkQ.baseChange B (1 ⊗ (1 ⊗ x j)) = 1 ⊗ N.mkQ (1 ⊗ x j)
  simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
    Submodule.mkQ_apply]

def chartFunctor (x : Fin k → M) : CommAlgCat.{w, u} R ⥤ Type (max v w) where
  obj A := { N : G(k, A ⊗[R] M; A) // Function.Bijective <| N.mkQ ∘ₗ asdf k R M A x}
  map {A B} f := by
    algebraize [f.hom.toRingHom]
    exact fun N => ⟨Grassmannian.map A B N.val, by
      rcases N with ⟨N, hN⟩
      exact map_chart_bijective k R M A B x N hN
    ⟩
  map_id A := by
    ext1 N
    simp only [types_id_apply, map_id]
  map_comp {A B C} f g := by
    algebraize [f.hom.toRingHom, g.hom.toRingHom, (f ≫ g).hom.toRingHom]
    haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' (by
      ext a
      change ((g.hom.comp f.hom) a) = g.hom (f.hom a)
      simp [AlgHom.comp_apply])
    ext1 N
    exact Subtype.ext (map_comp R M k N.val)

#check Subfunctor

def chartSubFunctor (x : Fin k → M) : Subfunctor (functor R M k) where
  obj A := { N : G(k, A ⊗[R] M; A) | Function.Bijective <| N.mkQ ∘ₗ asdf k R M A x}
  map := sorry

def subFunctorNatTrans (x : Fin k → M) : chartFunctor k R M x ⟶ functor R M k where
  app _ N := N.val
  naturality _ _ _ := rfl

-- TODO: Figure out how to say this is a subfunctor

end Chart

end Grassmannian

end Module

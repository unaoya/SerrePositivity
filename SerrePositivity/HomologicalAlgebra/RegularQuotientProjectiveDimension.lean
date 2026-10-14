/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module
public import SerrePositivity.HomologicalAlgebra.AuslanderBuchsbaum
public import Mathlib.RingTheory.Regular.Free

/-! # Projective dimension under a common regular quotient

Adapted from mathlib commit `9c971a554fb6265f06b80bc62c7b314f4f2d33ec`.
Original license and authors above.
-/
@[expose] public section
namespace SerrePositivity.RegularQuotientProjectiveDimension
universe u v

variable (R : Type u) [CommRing R]

open IsLocalRing CategoryTheory RingTheory.Sequence

section

variable {R} (x : R) {M N L : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
    [Module R M] [Module R N] [Module R L]

/-- The linear map `M⧸xM →ₗ[R] N⧸xN` induced by a linear map `M →ₗ[R] N`. -/
def QuotSMulTopMap (f : M →ₗ[R] N) :
    QuotSMulTop x M →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x N where
  __ := Submodule.mapQ _ _ f (fun m hm ↦ by
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm with ⟨m', _, hm'⟩
    simpa [← hm'] using Submodule.smul_mem_pointwise_smul _ x ⊤ trivial)
  map_smul' r m := by
    rcases Ideal.Quotient.mk_surjective r with ⟨s, rfl⟩
    exact map_smul (Submodule.mapQ _ _ f _) s m

lemma quotSMulTopMap_surjective {f : M →ₗ[R] N} (surj : Function.Surjective f) :
    Function.Surjective (QuotSMulTopMap x f) :=
  QuotSMulTop.map_surjective x surj

lemma quotSMulTopMap_exact {f : M →ₗ[R] N} {g : N →ₗ[R] L} (exact : Function.Exact f g)
    (surj : Function.Surjective g) :
    Function.Exact (QuotSMulTopMap x f) (QuotSMulTopMap x g) :=
  QuotSMulTop.map_exact x exact surj

end

variable {R} in
lemma IsSMulRegular.of_free {x : R} (reg : IsSMulRegular R x) (M : Type*) [AddCommGroup M]
    [Module R M] [free : Module.Free R M] : IsSMulRegular M x := by
  rcases free with ⟨⟨I, ⟨e⟩⟩⟩
  rw [e.isSMulRegular_congr]
  apply IsSMulRegular.of_right_eq_zero_of_smul (fun y hy ↦ ?_)
  ext i
  apply reg.right_eq_zero_of_smul
  rw [← Finsupp.smul_apply, hy, Finsupp.zero_apply]

open Ideal in
lemma projectiveDimension_eq_quotient [Small.{v} R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] (x : R)
    (reg1 : IsSMulRegular R x) (reg2 : IsSMulRegular M x)
    (mem : x ∈ maximalIdeal R) : projectiveDimension.{v} M =
    projectiveDimension.{v} (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) := by
  have aux (n : ℕ): projectiveDimension M ≤ n ↔
    projectiveDimension.{v} (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) ≤ n := by
    simp only [projectiveDimension_le_iff]
    induction n generalizing M with
    | zero =>
      simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
      rw [← IsProjective.iff_projective, ← IsProjective.iff_projective]
      have := Module.finitePresentation_of_finite R M
      have := Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · have := (Module.free_quotSMulTop_iff_free R M (maximalIdeal_le_jacobson _ mem) reg2).mpr
          Module.free_of_flat_of_isLocalRing
        exact Module.Projective.of_free
      · have : IsLocalRing (R ⧸ Ideal.span {x}) :=
          have : Nontrivial (R ⧸ Ideal.span {x}) :=
            Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
          IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
        have := (Module.free_quotSMulTop_iff_free R M (maximalIdeal_le_jacobson _ mem) reg2).mp
          Module.free_of_flat_of_isLocalRing
        exact Module.Projective.of_free
    | succ n ih =>
      obtain ⟨N, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R M
      let S := f.shortComplexKer
      have S_exact := LinearMap.shortExact_shortComplexKer surjf
      have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
      have reg2'' : IsSMulRegular S.X₂ x := IsSMulRegular.of_free reg1 S.X₂
      have reg2' : IsSMulRegular S.X₁ x := reg2''.submodule _ _
      have Sx_exact' := quotSMulTopMap_exact x f.exact_subtype_ker_map surjf
      let Sx := ModuleCat.shortComplexOfCompEqZero (QuotSMulTopMap x (LinearMap.ker f).subtype)
        (QuotSMulTopMap x f) Sx_exact'.linearMap_comp_eq_zero
      have inj : Function.Injective (QuotSMulTopMap x (LinearMap.ker f).subtype) := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro y hy
        rcases Submodule.Quotient.mk_surjective _ y with ⟨y', hy'⟩
        simp only [QuotSMulTopMap, ← hy', LinearMap.mem_ker, LinearMap.coe_mk,
          LinearMap.coe_toAddHom, Submodule.mapQ_apply, Submodule.subtype_apply,
          Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hy
        rcases hy with ⟨z, _, hz⟩
        have := y'.2
        rw [← hz, LinearMap.mem_ker, map_smul] at this
        simp only [← hy', Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists,
          Submodule.mem_top, true_and, Subtype.exists, SetLike.mk_smul_mk, LinearMap.mem_ker]
        use z, reg2.right_eq_zero_of_smul this
        exact Subtype.val_inj.mp hz
      have Sx_exact := ModuleCat.shortComplex_shortExact Sx Sx_exact' inj
        (quotSMulTopMap_surjective x surjf)
      have := Module.finitePresentation_of_finite R N
      exact ((S_exact.hasProjectiveDimensionLT_X₃_iff n proj).trans (ih S.X₁ reg2')).trans
        (Sx_exact.hasProjectiveDimensionLT_X₃_iff n inferInstance).symm
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, projectiveDimension_eq_bot_iff,
      projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun h ↦ (Submodule.Quotient.mk_surjective _).subsingleton, fun h ↦ ?_⟩
    by_contra! ntr
    exact (not_subsingleton_iff_nontrivial.mpr (nontrivial_quotSMulTop_of_mem_maximalIdeal M mem)) h
  | coe N =>
    induction N with
    | top => simp
    | coe n => exact aux n

end SerrePositivity.RegularQuotientProjectiveDimension

namespace SerrePositivity
open CategoryTheory
/-- Quotienting by a common regular element preserves projective dimension. -/
theorem projectiveDimension_eq_regularQuotient {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (M : ModuleCat.{u} R) [Module.Finite R M]
    (x : R) (hR : IsSMulRegular R x) (hM : IsSMulRegular M x)
    (hm : x ∈ IsLocalRing.maximalIdeal R) :
    projectiveDimension M = projectiveDimension
      (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :=
  RegularQuotientProjectiveDimension.projectiveDimension_eq_quotient R M x hR hM hm
end SerrePositivity

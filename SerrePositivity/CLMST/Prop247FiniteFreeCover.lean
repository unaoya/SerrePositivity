module

public import SerrePositivity.CLMST.Prop247FiniteFreeComparison
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedEtaleAwayCover
public import SerrePositivity.CommutativeAlgebra.DoubleLocalizationTensorComparison
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # Prop 2.4.7：実有限 étale 被覆上の有限自由比較

既存の局所分裂被覆を使い、各二重局所化の元の分裂同型から分母を払う。
perfectoid 化の almost 比較は使わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 実有限被覆の各部分で、元の局所代数同型を保つ有限自由比較と錐零化を構成する。
各部分の rank は異なってよく、rank 0 も排除しない。 -/
theorem prop247_exists_finiteFree_comparison_cover
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [IsReduced R]
    [Module.Finite R A] [Algebra.FinitePresentation R A]
    (hR : IsAbsolutelyIntegrallyClosed R) (g : R) :
    letI := GenericEtale.awayAlgebra R A g
    Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R A g)) →
      ∃ t : Finset (Localization.Away g),
        Ideal.span (t : Set (Localization.Away g)) = ⊤ ∧
        (∃ N : ℕ, g ^ N ∈ Ideal.span (Set.range (fun f : t =>
          g * (IsLocalization.Away.sec g f.1).1))) ∧
        ∀ f ∈ t, ∃ (r : ℕ)
          (e : (Localization.Away f) ⊗[Localization.Away g]
            (Localization.Away (algebraMap R A g)) ≃ₐ[Localization.Away f]
              (Fin r → Localization.Away f))
          (k : ℕ) (u : A →ₗ[R] (Fin r → R)),
          (∀ a i, algebraMap R (Localization.Away f) (u a i) =
            (algebraMap R (Localization.Away f)
              (g * (IsLocalization.Away.sec g f).1)) ^ k *
              e ((1 : Localization.Away f) ⊗ₜ[Localization.Away g]
                algebraMap A (Localization.Away (algebraMap R A g)) a) i) ∧
          Function.Bijective (awayModuleMap (g * (IsLocalization.Away.sec g f).1) u) ∧
          ∃ q : ℕ, moduleMapConeScalar R u ((g * (IsLocalization.Away.sec g f).1) ^ q) = 0 ∧
            (∀ x : u.ker, (g * (IsLocalization.Away.sec g f).1) ^ q • x = 0) ∧
            (∀ y : (Fin r → R) ⧸ u.range,
              (g * (IsLocalization.Away.sec g f).1) ^ q • y = 0) := by
  letI := GenericEtale.awayAlgebra R A g
  intro hetale
  letI := Module.FinitePresentation.of_finite_of_finitePresentation R A
  obtain ⟨t, ht, hsplit, hcover⟩ := hR.finiteEtaleAway_exists_finite_cover g hetale
  refine ⟨t, ht, hcover, ?_⟩
  intro f hf
  obtain ⟨r, ⟨e⟩⟩ := hsplit f hf
  let d := g * (IsLocalization.Away.sec g f).1
  letI : IsLocalization (.powers d) (Localization.Away f) :=
    principalLocalizationTower_isLocalization g f
  let e' := (doubleLocalizationTensorEquiv R A g f).trans e
  obtain ⟨k, u, he, hu, hq⟩ :=
    prop247_exists_finiteFree_comparison_of_tensor_equiv d (Localization.Away f) r
      e'.toLinearEquiv
  refine ⟨r, e, k, u, ?_, hu, hq⟩
  intro a i
  have h := he a i
  change algebraMap R (Localization.Away f) (u a i) =
    (algebraMap R (Localization.Away f) d) ^ k *
      e (doubleLocalizationTensorEquiv R A g f ((1 : Localization.Away f) ⊗ₜ[R] a)) i at h
  rw [doubleLocalizationTensorEquiv_tmul] at h
  exact h

end SerrePositivity.CLMST

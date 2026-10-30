module

public import SerrePositivity.CLMST.Prop247AicRankCoefficients
public import SerrePositivity.CLMST.Prop247RankAssembly
public import SerrePositivity.CommutativeAlgebra.Localization.CommonModel
public import SerrePositivity.CommutativeAlgebra.Localization.Away
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # Prop 2.4.7：元の S→∏Si の付値環条件

実係数比較の零化を通常 tensor の元の単位へ移し、既存の局所化判定と
整写像の一意延長を使う。付値環の perfectoid 性は要求しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 実係数写像の冪零化から、元の S→∏(Ti⊗R S) の局所化写像は全単射となる。 -/
theorem prop247_rankTensorUnit_away_bijective
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type} [Finite ι] (T : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)] (g : R) (a : ℕ)
    (hk : ∀ x : (Algebra.linearMap R ((i : ι) → T i)).ker, g ^ a • x = 0)
    (hc : ∀ y : ((i : ι) → T i) ⧸ (Algebra.linearMap R ((i : ι) → T i)).range,
      g ^ a • y = 0) :
    Function.Bijective (Localization.awayMap (prop247_rankTensorUnit R S T).toRingHom
      (algebraMap R S g)) := by
  let f := prop247_rankTensorUnit R S T
  obtain ⟨hsk, hsc⟩ := prop247_rankTensorUnit_ker_coker R S T (g ^ a) hk hc
  apply localizationComparison_awayMap_bijective_of_power_bounds g f
  · intro x hx
    refine ⟨a * 2, ?_⟩
    have h := congrArg Subtype.val (hsk ⟨x, hx⟩)
    change (g ^ a) ^ 2 • x = 0 at h
    simpa only [pow_mul] using h
  · intro y
    refine ⟨a * 2, ?_⟩
    apply (Submodule.Quotient.mk_eq_zero f.toLinearMap.range).mp
    change f.toLinearMap.range.mkQ (g ^ (a * 2) • y) = 0
    rw [map_smul]
    simpa only [pow_mul] using hsc (f.toLinearMap.range.mkQ y)

/-- 原典の S→∏Si は任意の付値環への元の写像を一意に延長する。
V の rank・離散性・完備性や perfectoid 性は仮定しない。 -/
theorem prop247_aic_rankSourceProduct_valuation_extension
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ) (ht : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x ∈ t)
    (T : t → Type u) [∀ n : t, CommRing (T n)] [∀ n : t, Algebra R (T n)]
    [∀ n : t, Algebra (prop247_rankSourceImage R S g hetale n) (T n)]
    [∀ n : t, IsScalarTower R (prop247_rankSourceImage R S g hetale n) (T n)]
    (hf : ∀ n : t, IsPerfectoidization p
      (algebraMap (prop247_rankSourceImage R S g hetale n) (T n)))
    (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra S V]
    (hg : algebraMap S V (algebraMap R S g) ≠ 0) :
    ∃! l : ((n : t) → T n ⊗[R] S) →+* V,
      l.comp (prop247_rankTensorUnit R S T).toRingHom = algebraMap S V := by
  let f := prop247_rankTensorUnit R S T
  let X := (n : t) → T n ⊗[R] S
  letI : Algebra S X := f.toRingHom.toAlgebra
  letI : IsScalarTower R S X := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  letI (n : t) : Module.Finite R (T n) :=
    (prop247_rankTarget_surjective_finite R S p hR g hetale n (T n) (hf n)).2
  letI : Module.Finite R X := inferInstance
  letI : Module.Finite S X := Module.Finite.of_restrictScalars_finite R S X
  obtain ⟨a, hk, hc⟩ :=
    prop247_aic_rankCoefficient_annihilators R S p hR hAIC g hetale t ht T hf
  have hiso := prop247_rankTensorUnit_away_bijective R S T g a hk hc
  exact existsUnique_valuation_extension_of_integral_away_bijective S X V
    (algebraMap R S g) hg hiso

end SerrePositivity.CLMST

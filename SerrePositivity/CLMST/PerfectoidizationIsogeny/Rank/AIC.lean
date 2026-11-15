module

public import SerrePositivity.CommutativeAlgebra.RankLocus
public import SerrePositivity.CommutativeAlgebra.ReducedSpectrum
public import SerrePositivity.BhattScholze.Semiperfectoid.Surjectivity.AbsolutelyIntegrallyClosedQuotient
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Rank.Diagram
public import SerrePositivity.HomologicalAlgebra.FiniteFreeComparison
public import SerrePositivity.HomologicalAlgebra.ScalarConeAnnihilators

/-! # André 基底の上の階数の係数比較

## 概要

André 基底の上では、元の階数の開集合を `D(d)` と表して切断への像を `R/Ann(d)` と同定でき、階数の像は既に perfectoid である（`aic_rankImage_isIntegralPerfectoid`）。perfectoid 化の単位の全単射性で通常の階数の直積の錐の零化を `R → ∏ T_i` へ移し（`aic_rankCoefficient_annihilators`）、係数の入力を供給した組み立てを与える。

## 方針

絶対整閉な perfectoid 環の零化商の定理（BhattScholze/Semiperfectoid/Surjectivity/AbsolutelyIntegrallyClosedQuotient）を当てる。

## 規約

CLMST Prop 2.4.7。終域の比較の核と各成分の同種性は明示的な入力として残す。旧 `CLMST/Prop247AicRankImages`・`Prop247AicRankCoefficients`・`Prop247AicRankAssembly`。

## 使われ方

`Rank/ComponentExcision`。
-/

@[expose] public noncomputable section

universe u

section Prop247AicRankImagesPart

namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false

/-- André 基底上では各元の Ri 自身が perfectoid である。 -/
theorem aic_rankImage_isIntegralPerfectoid
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ) :
    IsIntegralPerfectoid (openSectionImage R (rankOpen R S g hetale n)) p := by
  letI := hR.isReduced R p
  obtain ⟨a, ha⟩ := rankOpen_exists_basicOpen R S g hetale n
  have hI : PrimeSpectrum.vanishingIdeal
      (rankOpen R S g hetale n : Set (PrimeSpectrum R)) =
      (Ideal.span {g * a}).annihilator := by
    rw [ha]
    exact vanishingIdeal_basicOpen_eq_annihilator R (g * a)
  let e := (Ideal.quotientEquivAlgOfEq R hI.symm).trans
    (openSectionImageQuotientEquiv R (rankOpen R S g hetale n))
  exact BhattScholze.isIntegralPerfectoid_of_ringEquiv p e.toRingEquiv
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.aicPerfectoid_annihilatorPrincipalQuotient R p hR hAIC (g * a))

/-- 各 Ri の指定 perfectoid 化単位そのものが全単射である。 -/
theorem aic_rankTarget_unit_bijective
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ)
    (T : Type u) [CommRing T]
    (f : openSectionImage R (rankOpen R S g hetale n) →+* T)
    (hf : IsPerfectoidization p f) : Function.Bijective f := by
  have hI := aic_rankImage_isIntegralPerfectoid R S p hR hAIC g hetale n
  obtain ⟨e, he⟩ := hI.isPerfectoidization_id.exists_equiv p hf
  have he' : e.toRingHom = f := by simpa only [RingHom.comp_id] using he
  rw [← he']
  exact e.bijective

end SerrePositivity.CLMST

end Prop247AicRankImagesPart

section Prop247AicRankCoefficientsPart

namespace SerrePositivity.CLMST
set_option backward.isDefEq.respectTransparency false

/-- 原典の実 rank 係数写像の核・余核は、一つの g の冪で零化される。 -/
theorem aic_rankCoefficient_annihilators
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ) (ht : ∀ x : PrimeSpectrum.basicOpen g, awayRank R S g x ∈ t)
    (T : t → Type u) [∀ n : t, CommRing (T n)] [∀ n : t, Algebra R (T n)]
    [∀ n : t, Algebra (rankSourceImage R S g hetale n) (T n)]
    [∀ n : t, IsScalarTower R (rankSourceImage R S g hetale n) (T n)]
    (hf : ∀ n : t, IsPerfectoidization p
      (algebraMap (rankSourceImage R S g hetale n) (T n))) :
    ∃ q : ℕ,
      (∀ x : (Algebra.linearMap R ((n : t) → T n)).ker, g ^ q • x = 0) ∧
      (∀ y : ((n : t) → T n) ⧸ (Algebra.linearMap R ((n : t) → T n)).range,
        g ^ q • y = 0) := by
  letI := hR.isReduced R p
  let u := (toRankImageProduct R S g hetale t).toLinearMap
  let e := (rankTargetProductMap R S g hetale t T).toLinearMap
  let f := Algebra.linearMap R ((n : t) → T n)
  have he : Function.Bijective e :=
    Function.Bijective.piMap (fun n : t =>
      aic_rankTarget_unit_bijective R S p hR hAIC g hetale n (T n)
        (algebraMap (rankSourceImage R S g hetale n) (T n)) (hf n))
  obtain ⟨q, hq⟩ := rankImageProduct_cone_isogeny R S g hetale t ht
  obtain ⟨huk, huc⟩ := moduleMapCone_pow_scalar_eq_zero_annihilates R u g q hq
  have hsq : (LinearMap.id : ((n : t) → T n) →ₗ[R] ((n : t) → T n)).comp f =
      e.comp u := by
    apply LinearMap.ext
    intro x
    exact (AlgHom.congr_fun (rankTargetProductMap_comp R S g hetale t T) x).symm
  have hek : ∀ x : e.ker, (1 : R) • x = 0 := by
    intro x
    apply Subtype.ext
    change (1 : R) • (x : rankImageProduct R S g hetale t) = 0
    simpa only [one_smul] using he.1 (x.property.trans (map_zero e).symm)
  have hec : ∀ y : ((n : t) → T n) ⧸ e.range, (1 : R) • y = 0 := by
    intro y
    obtain ⟨y, rfl⟩ := e.range.mkQ_surjective y
    obtain ⟨x, rfl⟩ := he.2 y
    rw [one_smul]
    exact (Submodule.Quotient.mk_eq_zero e.range).mpr ⟨x, rfl⟩
  have hik : ∀ x : (LinearMap.id : ((n : t) → T n) →ₗ[R] ((n : t) → T n)).ker,
      (1 : R) • x = 0 := by
    intro x
    apply Subtype.ext
    exact (one_smul R (x : (n : t) → T n)).trans x.property
  obtain ⟨hfk, hfc⟩ := ker_coker_annihilated_of_comparison_square f u e LinearMap.id hsq
    (g ^ q) (g ^ q) 1 1 1 huk huc hek hec hik
  exact ⟨q, by simpa only [mul_one] using hfk,
    by simpa only [one_mul, mul_one] using hfc⟩

end SerrePositivity.CLMST

end Prop247AicRankCoefficientsPart

section Prop247AicRankAssemblyPart

namespace SerrePositivity.CLMST
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 絶対整閉基底上では、残る終域比較と成分 isogeny から元の実錐へ合流する。
係数比較の冪零化・可換式・有限成分の共通指数は構成する。 -/
theorem aic_isogeny_of_rank_comparisons
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (t : Finset ℕ) (ht : ∀ x : PrimeSpectrum.basicOpen g, awayRank R S g x ∈ t)
    (T : t → Type u) [∀ n : t, CommRing (T n)] [∀ n : t, Algebra R (T n)]
    [∀ n : t, Algebra (rankSourceImage R S g hetale n) (T n)]
    [∀ n : t, IsScalarTower R (rankSourceImage R S g hetale n) (T n)]
    (hT : ∀ n : t, IsPerfectoidization p
      (algebraMap (rankSourceImage R S g hetale n) (T n)))
    (C : Type u) [CommRing C] [Algebra R C]
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (P : t → Type u) [∀ n : t, CommRing (P n)] [∀ n : t, Algebra R (P n)]
    (β : ∀ n : t, T n ⊗[R] S →ₐ[R] P n)
    (hβ : ∀ n : t, IsPerfectoidization p (β n).toRingHom)
    (htk : ∃ b : ℕ, ∀ x :
      (rankPerfectoidComparison R S T p C f hf P β hβ).toLinearMap.ker,
      g ^ b • x = 0)
    (hcomponent : ∀ n : t, ∃ q : ℕ,
      (∀ x : (β n).toLinearMap.ker, g ^ q • x = 0) ∧
        (∀ y : P n ⧸ (β n).toLinearMap.range, g ^ q • y = 0)) :
    ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
      (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
      (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  obtain ⟨a, hk, hc⟩ :=
    aic_rankCoefficient_annihilators R S p hR hAIC g hetale t ht T hT
  obtain ⟨b, htk⟩ := htk
  obtain ⟨q, hq⟩ := isogeny_of_actual_rank_comparisons R S T p C f hf P β hβ
    g a b hk hc htk hcomponent
  obtain ⟨hfk, hfc⟩ := moduleMapCone_pow_scalar_eq_zero_annihilates R f.toLinearMap g q hq
  exact ⟨q, hq, hfk, hfc⟩

end SerrePositivity.CLMST

end Prop247AicRankAssemblyPart

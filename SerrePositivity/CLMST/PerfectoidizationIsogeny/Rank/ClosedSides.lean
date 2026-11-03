module

public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Descent.StandardSquare
public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Rank.Diagram
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalIdeal
public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Rank.AIC
public import SerrePositivity.CommutativeAlgebra.Localization.CommonModel
public import SerrePositivity.CommutativeAlgebra.Localization.Away
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # 階数の四角の閉じた側の完備性と付値環の条件

## 概要

`S → ∏ S_i` と `I = (g)` の像を固定し、離散な環の四頂点と二つのイデアルの導来 p 完備性を示す（`rankSource_closedSide_completeness`）。係数の比較の零化を通常のテンソルの単位へ移し、付値環への一意な延長の条件を与える（`aic_rankSourceProduct_valuation_extension`）。

## 方針

局所化の判定と整写像の一意な延長（CommutativeAlgebra/Localization/Away）を使う。付値環の perfectoid 性は要らない。

## 規約

CLMST Prop 2.4.7。BS Cor 8.12 の E∞ の四角の引き戻し性は主張しない。旧 `CLMST/Prop247RankClosedSides`・`Prop247RankSourceValuation`。

## 使われ方

`Proof`。
-/

@[expose] public noncomputable section

universe u v

section Prop247RankClosedSidesPart

namespace SerrePositivity.CLMST
open DerivedCompletion
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- 原典の実 rank 底変換写像と元の主イデアルについて、離散な閉側の完備入力を供給する。 -/
theorem rankSource_closedSide_completeness
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : R)
    {ι : Type} [Finite ι] (T : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    (hT : ∀ i, IsIntegralPerfectoid (T i) p) :
    let X := (i : ι) → T i ⊗[R] S
    let I := Ideal.span {algebraMap R S g}
    let J := I.map (rankTensorUnit R S T).toRingHom
    IsModuleComplete S (p : S) (ModuleCat.of S S) ∧
      IsModuleComplete X (p : X) (ModuleCat.of X X) ∧
      IsModuleComplete S (p : S) (ModuleCat.of S I) ∧
      IsModuleComplete X (p : X) (ModuleCat.of X J) ∧
      IsModuleComplete (S ⧸ I) (p : S ⧸ I) (ModuleCat.of (S ⧸ I) (S ⧸ I)) ∧
      IsModuleComplete (X ⧸ J) (p : X ⧸ J) (ModuleCat.of (X ⧸ J) (X ⧸ J)) := by
  let X := (i : ι) → T i ⊗[R] S
  let I := Ideal.span {algebraMap R S g}
  let J := I.map (rankTensorUnit R S T).toRingHom
  have hS : IsModuleComplete S (p : S) (ModuleCat.of S S) := by
    have h := (isModuleComplete_algebraMap_iff R S (p : R) S).mpr
      (source_isModuleComplete R S p hR)
    simpa only [map_natCast] using h
  have hX : IsModuleComplete X (p : X) (ModuleCat.of X X) := by
    have h := (isModuleComplete_algebraMap_iff R X (p : R) X).mpr
      (rankBaseChangeProduct_isModuleComplete R p T hT S)
    simpa only [map_natCast] using h
  have hJ : J = Ideal.span {algebraMap R X g} := by
    change (Ideal.span {algebraMap R S g}).map (rankTensorUnit R S T).toRingHom = _
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x : X => Ideal.span {x}) ((rankTensorUnit R S T).commutes g)
  refine ⟨hS, hX, isModuleComplete_principal_ideal S (p : S) (algebraMap R S g) hS, ?_,
    isModuleComplete_principal_quotient_natCast S p (algebraMap R S g) hS, ?_⟩
  · change IsModuleComplete X (p : X) (ModuleCat.of X J)
    rw [hJ]
    exact isModuleComplete_principal_ideal X (p : X) (algebraMap R X g) hX
  · change IsModuleComplete (X ⧸ J) (p : X ⧸ J) (ModuleCat.of (X ⧸ J) (X ⧸ J))
    rw [hJ]
    exact isModuleComplete_principal_quotient_natCast X p (algebraMap R X g) hX

end SerrePositivity.CLMST

end Prop247RankClosedSidesPart

section Prop247RankSourceValuationPart

namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 実係数写像の冪零化から、元の S→∏(Ti⊗R S) の局所化写像は全単射となる。 -/
theorem rankTensorUnit_away_bijective
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {ι : Type} [Finite ι] (T : ι → Type u)
    [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)] (g : R) (a : ℕ)
    (hk : ∀ x : (Algebra.linearMap R ((i : ι) → T i)).ker, g ^ a • x = 0)
    (hc : ∀ y : ((i : ι) → T i) ⧸ (Algebra.linearMap R ((i : ι) → T i)).range,
      g ^ a • y = 0) :
    Function.Bijective (Localization.awayMap (rankTensorUnit R S T).toRingHom
      (algebraMap R S g)) := by
  let f := rankTensorUnit R S T
  obtain ⟨hsk, hsc⟩ := rankTensorUnit_ker_coker R S T (g ^ a) hk hc
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
theorem aic_rankSourceProduct_valuation_extension
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
      (algebraMap (rankSourceImage R S g hetale n) (T n)))
    (V : Type v) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra S V]
    (hg : algebraMap S V (algebraMap R S g) ≠ 0) :
    ∃! l : ((n : t) → T n ⊗[R] S) →+* V,
      l.comp (rankTensorUnit R S T).toRingHom = algebraMap S V := by
  let f := rankTensorUnit R S T
  let X := (n : t) → T n ⊗[R] S
  letI : Algebra S X := f.toRingHom.toAlgebra
  letI : IsScalarTower R S X := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  letI (n : t) : Module.Finite R (T n) :=
    (rankTarget_surjective_finite R S p hR g hetale n (T n) (hf n)).2
  letI : Module.Finite R X := inferInstance
  letI : Module.Finite S X := Module.Finite.of_restrictScalars_finite R S X
  obtain ⟨a, hk, hc⟩ :=
    aic_rankCoefficient_annihilators R S p hR hAIC g hetale t ht T hf
  have hiso := rankTensorUnit_away_bijective R S T g a hk hc
  exact existsUnique_valuation_extension_of_integral_away_bijective S X V
    (algebraMap R S g) hg hiso

end SerrePositivity.CLMST

end Prop247RankSourceValuationPart

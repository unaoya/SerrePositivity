module

public import SerrePositivity.CLMST.PerfectoidizationIsogeny.ConstantRank
public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Rank.Targets
public import SerrePositivity.CLMST.PerfectoidizationIsogeny.Rank.AIC
public import SerrePositivity.CommutativeAlgebra.Localization.EtaleAway
public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # 各階数成分への定数階数の結果の適用

## 概要

各成分 `S_i = T_i ⊗_R S` の有限性・有限表示性・定数階数と `T_i` の絶対整閉性を供給して定数階数の結果を当て、結論を指定した `β_i` と元の `R` の作用の核・余核へ戻す。原典の階数の比較のデータ（有限な階数の集合、`R_i` と `S_i` の perfectoid 化）を選ぶ（`aic_exists_rank_comparison_data`）。

## 方針

存在の選択には BS の B3 と既存の整代数の perfectoid 化だけを使う。

## 規約

CLMST Prop 2.4.7。excision は明示的な入力。旧 `CLMST/Prop247RankComponentExcision`・`Prop247RankData`。

## 使われ方

`GeneralRank`。
-/

@[expose] public noncomputable section

universe u

section Prop247RankComponentExcisionPart

namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 原典の各実 rank 成分の指定単位について、KL excision から元の R 作用の冪零化を得る。
Si の bounded torsion は不要である。 -/
theorem aic_rankComponent_annihilators_of_excision
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (n : ℕ) (T P : Type u) [CommRing T] [CommRing P] [Algebra R T] [Algebra R P]
    [Algebra (rankSourceImage R S g hetale n) T]
    [IsScalarTower R (rankSourceImage R S g hetale n) T]
    (hT : IsPerfectoidization p (algebraMap (rankSourceImage R S g hetale n) T))
    (hExcision : BhattScholze.KLFiniteComparisonExcision T p)
    (β : T ⊗[R] S →ₐ[R] P) (hβ : IsPerfectoidization p β.toRingHom) :
    ∃ q : ℕ, (∀ x : β.toLinearMap.ker, g ^ q • x = 0) ∧
      (∀ y : P ⧸ β.toLinearMap.range, g ^ q • y = 0) := by
  letI := hR.isReduced R p
  letI : Algebra T P := (β.toRingHom.comp (algebraMap T (T ⊗[R] S))).toAlgebra
  letI : IsScalarTower R T P := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R P r = β (algebraMap T (T ⊗[R] S) (algebraMap R T r))
    rw [← IsScalarTower.algebraMap_apply R T (T ⊗[R] S), β.commutes]
  let βT : T ⊗[R] S →ₐ[T] P := { β.toRingHom with commutes' := fun _ => rfl }
  have hβT : IsPerfectoidization p βT.toRingHom := hβ
  have hAIC_T := rankTarget_isAbsolutelyIntegrallyClosed R S p hR hAIC g hetale n T hT
  have hRank := awayRank_baseChange_over_rankImage R S g hetale n T
  have hEtale := etaleAway_tensor_baseChange (R := R) (A := S) (B := T) g hetale
  obtain ⟨q, hq⟩ := aic_constantRank_isogeny_of_finiteComparison_excision p hT.1
    hAIC_T hExcision (algebraMap R T g) βT hβT hEtale n hRank
  obtain ⟨hk, hc⟩ := moduleMapCone_pow_scalar_eq_zero_annihilates T βT.toLinearMap
    (algebraMap R T g) q hq
  refine ⟨q, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    change g ^ q • (x : T ⊗[R] S) = 0
    have h := congrArg Subtype.val (hk ⟨(x : T ⊗[R] S), x.property⟩)
    change (algebraMap R T g) ^ q • (x : T ⊗[R] S) = 0 at h
    simpa only [← map_pow, algebraMap_smul] using h
  · intro y
    obtain ⟨y, rfl⟩ := β.toLinearMap.range.mkQ_surjective y
    have hy : (algebraMap R T g) ^ q • y ∈ βT.toLinearMap.range := by
      apply (Submodule.Quotient.mk_eq_zero βT.toLinearMap.range).mp
      exact (βT.toLinearMap.range.mkQ.map_smul ((algebraMap R T g) ^ q) y).trans (hc _)
    obtain ⟨x, hx⟩ := hy
    rw [← map_smul]
    apply (Submodule.Quotient.mk_eq_zero β.toLinearMap.range).mpr
    refine ⟨x, ?_⟩
    change β x = g ^ q • y
    change β x = (algebraMap R T g) ^ q • y at hx
    simpa only [← map_pow, algebraMap_smul] using hx

/-- 元の実 rank 分解に各定 rank 証明を適用する。
成分 isogeny と係数零化を構成し、残る入力は元の終域比較の核の冪零化だけである。 -/
theorem aic_isogeny_of_rank_component_excision
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
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
    (hExcision : ∀ n : t, BhattScholze.KLFiniteComparisonExcision (T n) p)
    (C : Type u) [CommRing C] [Algebra R C]
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
    (P : t → Type u) [∀ n : t, CommRing (P n)] [∀ n : t, Algebra R (P n)]
    (β : ∀ n : t, T n ⊗[R] S →ₐ[R] P n)
    (hβ : ∀ n : t, IsPerfectoidization p (β n).toRingHom)
    (htk : ∃ b : ℕ, ∀ x :
      (rankPerfectoidComparison R S T p C f hf P β hβ).toLinearMap.ker,
      g ^ b • x = 0) :
    ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
      (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
      (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  apply aic_isogeny_of_rank_comparisons R S p hR hAIC g hetale t ht T hT
    C f hf P β hβ htk
  intro n
  exact aic_rankComponent_annihilators_of_excision R S p hR hAIC g hetale n
    (T n) (P n) (hT n) (hExcision n) (β n) (hβ n)

end SerrePositivity.CLMST

end Prop247RankComponentExcisionPart

section Prop247RankDataPart

namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 原典の実 rank 対象と単位を選び、終域比較の核の冪零化から元の錐へ接続する。
各対象の元の R 代数構造は CommAlgCat に保持し、対象の存在を仮定しない。 -/
theorem aic_exists_rank_comparison_data
    (R S C : Type u) [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra R C] [Module.Finite R S] [Algebra.FinitePresentation R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R)
    (hExcision : ∀ (B : Type u) [CommRing B], IsIntegralPerfectoid B p →
      IsAbsolutelyIntegrallyClosed B → BhattScholze.KLFiniteComparisonExcision B p)
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (f : S →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom) :
    ∃ (t : Finset ℕ) (_ : ∀ x : PrimeSpectrum.basicOpen g, awayRank R S g x ∈ t)
      (T : t → CommAlgCat.{u} R)
      (u : ∀ n : t, rankSourceImage R S g hetale n →ₐ[R] T n)
      (_ : ∀ n : t, IsPerfectoidization p (u n).toRingHom)
      (P : t → CommAlgCat.{u} R)
      (β : ∀ n : t, T n ⊗[R] S →ₐ[R] P n)
      (hβ : ∀ n : t, IsPerfectoidization p (β n).toRingHom),
      (∃ b : ℕ, ∀ x : (rankPerfectoidComparison R S
        (fun n => T n) p C f hf (fun n => P n) β hβ).toLinearMap.ker, g ^ b • x = 0) →
      ∃ q : ℕ, moduleMapConeScalar R f.toLinearMap (g ^ q) = 0 ∧
        (∀ x : f.toLinearMap.ker, g ^ q • x = 0) ∧
        (∀ y : C ⧸ f.toLinearMap.range, g ^ q • y = 0) := by
  classical
  obtain ⟨t, _ht, _hc, hcover, _hd⟩ :=
    awayRank_finite_clopen_decomposition R S g hetale
  have htargets (n : t) : ∃ (T : CommAlgCat.{u} R)
      (u : rankSourceImage R S g hetale n →ₐ[R] T),
      IsPerfectoidization p u.toRingHom := by
    obtain ⟨T, hT, hRT, hIT, htower, hf, _hs, _hfin, _hrank⟩ :=
      rankImage_exists_perfectoid_target R S p hR g hetale n
    letI := hT
    letI := hRT
    letI := hIT
    letI := htower
    exact ⟨CommAlgCat.of R T,
      IsScalarTower.toAlgHom R (rankSourceImage R S g hetale n) T, hf⟩
  choose T u hu using htargets
  letI (n : t) : Algebra (rankSourceImage R S g hetale n) (T n) :=
    (u n).toRingHom.toAlgebra
  letI (n : t) : IsScalarTower R (rankSourceImage R S g hetale n) (T n) :=
    IsScalarTower.of_algHom (u n)
  have hT (n : t) : IsPerfectoidization p
      (algebraMap (rankSourceImage R S g hetale n) (T n)) := hu n
  have hperfectoid (n : t) : ∃ (P : CommAlgCat.{u} R)
      (β : T n ⊗[R] S →ₐ[R] P), IsPerfectoidization p β.toRingHom := by
    obtain ⟨P, hP, β₀, hβ₀⟩ := BhattScholze.Inputs.exists_perfectoidization_of_integral
      (T n) (T n ⊗[R] S) p (hT n).1
    letI := hP
    letI : Algebra R P := (β₀.comp (algebraMap R (T n ⊗[R] S))).toAlgebra
    exact ⟨CommAlgCat.of R P, { β₀ with commutes' := fun _ => rfl }, hβ₀⟩
  choose P β hβ using hperfectoid
  refine ⟨t, hcover, T, u, hu, P, β, hβ, ?_⟩
  intro htk
  apply aic_isogeny_of_rank_component_excision R S p hR hAIC g hetale t hcover
    (fun n => T n) hT ?_ C f hf (fun n => P n) β hβ htk
  intro n
  exact hExcision (T n) (hT n).1
    (rankTarget_isAbsolutelyIntegrallyClosed R S p hR hAIC g hetale n (T n) (hT n))

end SerrePositivity.CLMST

end Prop247RankDataPart

module

public import SerrePositivity.CommutativeAlgebra.RankLocus
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.SurjectiveQuotientPerfectoidization
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic

/-! # 階数の像の perfectoid 化の対象

## 概要

原典の階数の像 `R_i` の perfectoid 化の対象 `T_i` を、`R_i` の有限表示性や完備性を仮定せずに作り、全射性・有限性・基底変更の定数階数を保つ（`rankImage_exists_perfectoid_target`）。André 拡大の絶対整閉性を `T_i` へ渡す（`rankImage_exists_aic_perfectoid_target`）。

## 方針

BS の B3・B4 と、全射像の絶対整閉性の一般論を使う。

## 規約

CLMST Prop 2.4.7 の階数ごとの分解。BS Cor 8.12 や perfectoid 化の後の almost 比較は使わない。旧 `CLMST/Prop247RankTargets`・`Prop247RankAIC`。

## 使われ方

`Rank/Diagram`・`Rank/AIC`。
-/

@[expose] public noncomputable section

universe u

section Prop247RankTargetsPart

namespace SerrePositivity.CLMST
open scoped _root_.TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- 指定した Ri の perfectoid 化は元の R の全射像であり、R 上有限である。 -/
theorem rankTarget_surjective_finite
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ)
    (T : Type u) [CommRing T] [Algebra R T]
    [Algebra (openSectionImage R (rankOpen R S g hetale n)) T]
    [IsScalarTower R (openSectionImage R (rankOpen R S g hetale n)) T]
    (hf : IsPerfectoidization p
      (algebraMap (openSectionImage R (rankOpen R S g hetale n)) T)) :
    Function.Surjective (algebraMap R T) ∧ Module.Finite R T := by
  let I := openSectionImage R (rankOpen R S g hetale n)
  let q := (toOpenSectionImage R (rankOpen R S g hetale n)).toRingHom
  have hq : Function.Surjective q := toOpenSectionImage_surjective R _
  have hf' := _root_.SerrePositivity.BhattScholze.Semiperfectoid.surjective_perfectoidization_of_quotient p hR q hq (algebraMap I T) hf
  have hs : Function.Surjective (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R I T]
    exact hf'.comp hq
  exact ⟨hs, Module.Finite.of_surjective (Algebra.linearMap R T) hs⟩

/-- 原典の各 Ri の実 perfectoid 化を、元の二つの代数作用・有限性・定 rank とともに供給する。
普遍対象の新しい存在引用は追加せず、既存 B3 と B4 を用いる。 -/
theorem rankImage_exists_perfectoid_target
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ) :
    let I := openSectionImage R (rankOpen R S g hetale n)
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra I T),
      IsScalarTower R I T ∧ IsPerfectoidization p (algebraMap I T) ∧
      Function.Surjective (algebraMap R T) ∧ Module.Finite R T ∧
      ∀ x : PrimeSpectrum.basicOpen (algebraMap R T g),
        awayRank T (T ⊗[R] S) (algebraMap R T g) x = n := by
  letI := hR.isReduced R p
  let I := openSectionImage R (rankOpen R S g hetale n)
  let q := (toOpenSectionImage R (rankOpen R S g hetale n)).toRingHom
  obtain ⟨T, hT, f, hf⟩ :=
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_perfectoid_surjective_quotient hR q
      (toOpenSectionImage_surjective R _)
  letI := hT
  letI : Algebra I T := f.toAlgebra
  letI : Algebra R T := (f.comp q).toAlgebra
  letI : IsScalarTower R I T := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨hs, hfinite⟩ := rankTarget_surjective_finite R S p hR g hetale n T hf
  refine ⟨T, hT, inferInstance, inferInstance, inferInstance, hf, hs, hfinite, ?_⟩
  intro x
  exact awayRank_baseChange_over_rankImage R S g hetale n T x

end SerrePositivity.CLMST

end Prop247RankTargetsPart

section Prop247RankAICPart

namespace SerrePositivity.CLMST

/-- André 基底の各実 rank 対象は絶対整閉である。Ri の有限表示性は不要。 -/
theorem rankTarget_isAbsolutelyIntegrallyClosed
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ)
    (T : Type u) [CommRing T] [Algebra R T]
    [Algebra (openSectionImage R (rankOpen R S g hetale n)) T]
    [IsScalarTower R (openSectionImage R (rankOpen R S g hetale n)) T]
    (hf : IsPerfectoidization p
      (algebraMap (openSectionImage R (rankOpen R S g hetale n)) T)) :
    IsAbsolutelyIntegrallyClosed T :=
  hAIC.of_surjective (algebraMap R T)
    (rankTarget_surjective_finite R S p hR g hetale n T hf).1

open scoped _root_.TensorProduct

/-- 元の rank 像の perfectoid 化を絶対整閉性と実底変換の定 rank とともに供給する。
原典の rank 0・空の rank 部分も含み、新しい存在引用を使わない。 -/
theorem rankImage_exists_aic_perfectoid_target
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (hAIC : IsAbsolutelyIntegrallyClosed R) (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ) :
    let I := openSectionImage R (rankOpen R S g hetale n)
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra I T),
      IsScalarTower R I T ∧ IsPerfectoidization p (algebraMap I T) ∧
      IsAbsolutelyIntegrallyClosed T ∧
      Function.Surjective (algebraMap R T) ∧ Module.Finite R T ∧
      ∀ x : PrimeSpectrum.basicOpen (algebraMap R T g),
        awayRank T (T ⊗[R] S) (algebraMap R T g) x = n := by
  obtain ⟨T, hT, hRT, hIT, htower, hf, hs, hfinite, hrank⟩ :=
    rankImage_exists_perfectoid_target R S p hR g hetale n
  letI := hT
  letI := hRT
  letI := hIT
  letI := htower
  exact ⟨T, hT, hRT, hIT, htower, hf,
    rankTarget_isAbsolutelyIntegrallyClosed R S p hR hAIC g hetale n T hf,
    hs, hfinite, hrank⟩

end SerrePositivity.CLMST

end Prop247RankAICPart

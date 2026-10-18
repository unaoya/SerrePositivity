module

public import SerrePositivity.KST.SchemeLemmas.NoetherianFiniteModuleFlattening
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# 整なアフィン基底の有限加群の生成点付近の自由化と平坦化

## 概要
Noether 整域上の有限加群を非空基本開で自由にし、既存の実際のチャート平坦化の入力を供給する。

## 方針
分数体上の自由基底を一つの非零元による局所化へ広げる。

## 規約
加群の純変換とスキームの strict transform の同定はまだ行わない。

## 使われ方
論文 補題 3.3、公理 (6) の有限射の Fitting 版平坦化のアフィン代数入力。
-/

@[expose] public section

universe u v

open scoped TensorProduct nonZeroDivisors
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- 概要：Noether 整域上の有限加群はある非零元の局所化で自由（論文 補題 3.3）。
方針：分数体での自由基底を有限表示性により一つの分母へ広げる。
規約：元の加群の平坦性や捩れなし性は要求しない。
使われ方：有限射を生成点の非空基本開で平坦にする入力。 -/
theorem exists_nonzero_away_free_of_finite :
    ∃ r : R, r ≠ 0 ∧ Module.Free (Localization.Away r) (LocalizedModule.Away r M) := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  let μ : M →ₗ[R] FractionRing R ⊗[R] M := TensorProduct.mk R (FractionRing R) M 1
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers R⁰ μ (FractionRing R)
  exact ⟨r, nonZeroDivisors.ne_zero hr, hfree⟩

/-- 概要：Noether 整域上の有限加群は非零境界の外で平坦（論文 補題 3.3）。
方針：同じ局所化を自由にする非零元を選び、自由加群の平坦性を使う。
規約：一般の有限型代数上の有限加群ではなく、基礎環上有限な加群を扱う。
使われ方：有限加群の実際の平坦化中心の存在定理への入力。 -/
theorem exists_nonzero_away_flat_of_finite :
    ∃ r : R, r ≠ 0 ∧ Module.Flat (Localization.Away r) (LocalizedModule.Away r M) := by
  obtain ⟨r, hr, hfree⟩ := exists_nonzero_away_free_of_finite R M
  have := hfree
  exact ⟨r, hr, inferInstance⟩

/-- 概要：Noether 整域上の有限加群には非空基本開を避ける実際のチャート平坦化中心がある（補題 3.3）。
方針：生成点付近の自由化から境界外の平坦性を供給し、実際の有限加群の中心構成を適用する。
規約：結論は全 blowup チャートの加群の純変換の平坦性。スキームの strict transform の平坦性とは区別する。
使われ方：公理 (6) の Fitting 版平坦化を実際のスキーム射へ接続する代数的な入力。 -/
theorem exists_nonzero_finite_module_flattening_center :
    ∃ (r : R) (J : Ideal R), r ≠ 0 ∧ J.FG ∧
      PrimeSpectrum.basicOpen r ≤ affineCenterComplement J ∧
      ∀ b : J, letI : Algebra R (BlowupChartRing J b) := (chartBaseMap J b).toAlgebra
        Module.Flat (BlowupChartRing J b)
          (modulePureTransform (chartBaseMap J b r) (BlowupChartRing J b ⊗[R] M)) := by
  obtain ⟨r, hr, hflat⟩ := exists_nonzero_away_flat_of_finite R M
  have := hflat
  obtain ⟨J, hJ, hU, hcharts⟩ := exists_noetherian_finite_flattening_center r
    (mem_nonZeroDivisors_iff_ne_zero.mpr hr) M
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
  exact ⟨r, J, hr, hJ, hU, hcharts⟩

end SerrePositivity.KST.Descent

module

public import SerrePositivity.KST.Descent.GenericFiniteFlattening
public import SerrePositivity.KST.Descent.AffineOpenPureTransform

/-!
# 有限代数の実際のアフィン像の平坦化チャート

## 概要
Noether 整域上の有限代数について、各実際の blowup チャート上の基本開のスキーム論的像を有限平坦にする。

## 方針
加群の平坦化中心を選び、純変換商の Spec との構造射を保つ同型で平坦性を移す。

## 規約
全射性や global strict transform の同定・貼り合わせはまだ結論しない。

## 使われ方
論文 補題 3.3、公理 (6) の実際の平坦化へ至るアフィンチャートの入力。
-/

@[expose] public section

universe u

open AlgebraicGeometry
open scoped TensorProduct
open SerrePositivity.KST.SchemeLemmas

namespace SerrePositivity.KST.Descent

variable (R B : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [CommRing B] [Algebra R B] [Module.Finite R B]

/-- 概要：有限代数には全 blowup チャートの実際の像を有限平坦にする中心がある（論文 補題 3.3）。
方針：生成点付近の自由化から加群の平坦化中心を取り、その純変換を実際の像の構造射に移す。
規約：像は基本開のスキーム論的像。global strict transform の平坦性には実際のチャート比較が必要。
使われ方：公理 (6) の有限射の平坦化をスキームとして貼り合わせるための局所的な結論。 -/
theorem exists_nonzero_finiteFlat_image_charts :
    ∃ (r : R) (J : Ideal R), r ≠ 0 ∧ J.FG ∧
      PrimeSpectrum.basicOpen r ≤ affineCenterComplement J ∧
      ∀ b : J, letI : Algebra R (BlowupChartRing J b) := (chartBaseMap J b).toAlgebra
        Flat (algebraBoundaryImageπ (BlowupChartRing J b)
          (BlowupChartRing J b ⊗[R] B) (chartBaseMap J b r)) ∧
        IsFinite (algebraBoundaryImageπ (BlowupChartRing J b)
          (BlowupChartRing J b ⊗[R] B) (chartBaseMap J b r)) := by
  obtain ⟨r, J, hr, hJ, hU, hcharts⟩ := exists_nonzero_finite_module_flattening_center R B
  refine ⟨r, J, hr, hJ, hU, ?_⟩
  intro b
  let : Algebra R (BlowupChartRing J b) := (chartBaseMap J b).toAlgebra
  have : Module.Flat (BlowupChartRing J b)
      (modulePureTransform (chartBaseMap J b r) (BlowupChartRing J b ⊗[R] B)) := hcharts b
  exact ⟨algebraBoundaryOpen_image_flat _ _ _, algebraBoundaryOpen_image_isFinite _ _ _⟩

end SerrePositivity.KST.Descent

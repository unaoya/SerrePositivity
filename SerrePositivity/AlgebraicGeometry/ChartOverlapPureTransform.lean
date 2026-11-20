module

public import SerrePositivity.AlgebraicGeometry.ChartOverlap
public import SerrePositivity.AlgebraicGeometry.TensorCoefficientLocalization

/-!
概要：KST §5、Stacks 0815 の標準チャートの重なり上での純変換の平坦性。
方針：二つの係数写像の一致を使い、第二チャートから重なりへ純変換を局所化する。
規約：重なりの R 代数構造は第一チャートからの係数写像で固定する。
使われ方：生成元チャート上の平坦性を任意のチャートへ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R : Type*} [CommRing R] (I : Ideal R) (a b : I)
  (f : R) (M : Type*) [AddCommGroup M] [Module R M]

/--
概要：第二チャートの純変換が平坦なら、重なり上の純変換も平坦。
方針：重なりが第二チャートの比の局所化であることを使い、境界の像の一致を照合する。
規約：KST §5、Stacks 0815、R から重なりへの係数写像は第一チャート経由。
使われ方：被覆チャートからの局所平坦性の移送。
-/
theorem chartOverlapPureTransform_flat_from_right
    (hb : letI : Algebra R (BlowupChartRing I b) := (chartBaseMap I b).toAlgebra
      Module.Flat (BlowupChartRing I b)
        (modulePureTransform (chartBaseMap I b f) (BlowupChartRing I b ⊗[R] M))) :
    letI : Algebra R (BlowupOverlapRing I a b) :=
      ((chartOverlapFromLeft I a b).comp (chartBaseMap I a)).toAlgebra
    Module.Flat (BlowupOverlapRing I a b)
      (modulePureTransform (chartOverlapFromLeft I a b (chartBaseMap I a f))
        (BlowupOverlapRing I a b ⊗[R] M)) := by
  let B := BlowupChartRing I b
  let D := BlowupOverlapRing I a b
  let : Algebra R B := (chartBaseMap I b).toAlgebra
  let : Algebra R D := ((chartOverlapFromLeft I a b).comp (chartBaseMap I a)).toAlgebra
  let : SMul R B := (inferInstance : Algebra R B).toSMul
  let : SMul R D := (inferInstance : Algebra R D).toSMul
  let : Algebra B D := (chartOverlapFromRight I a b).toAlgebra
  have : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq
    (fun r => chartOverlap_base I a b r)
  have : IsLocalization.Away (chartRatio I b a) D := chartOverlap_isLocalizationRight I a b
  have : Module.Flat B (modulePureTransform (chartBaseMap I b f) (B ⊗[R] M)) := hb
  have hflat := tensorPureTransformLocalization_flat R B D M
    (Submonoid.powers (chartRatio I b a)) (chartBaseMap I b f)
  change Module.Flat D
    (modulePureTransform (chartOverlapFromRight I a b (chartBaseMap I b f)) (D ⊗[R] M)) at hflat
  rw [← chartOverlap_base I a b f] at hflat
  exact hflat

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas

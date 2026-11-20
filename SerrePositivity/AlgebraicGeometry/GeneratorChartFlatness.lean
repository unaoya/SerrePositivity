module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartOverlapPureTransform
public import SerrePositivity.AlgebraicGeometry.ChartRatioGeneratorCover
public import SerrePositivity.AlgebraicGeometry.FlatLocalizationFamily

/-!
概要：KST §5、Stacks 0815 の生成元チャートから任意の標準チャートへの純変換の平坦性。
方針：生成元の比による被覆と、重なりへの純変換の局所化を使う。
規約：中心の生成族は有限とは限らない。
使われ方：行列式生成元チャートの自由化を全標準チャートでの平坦性へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R ι : Type*} [CommRing R] (I : Ideal R) (C : ι → I)
  (f : R) (M : Type*) [AddCommGroup M] [Module R M]

/--
概要：生成族の各チャート上の純変換が平坦なら全ての標準チャート上で平坦。
方針：固定チャートとの重なり上へ平坦性を移し、比が単位イデアルを生成する局所判定を使う。
規約：KST §5、Stacks 0815、全ての比較は実際の係数局所化写像。
使われ方：有限階数自由な境界外部分を持つ加群の平坦化。
-/
theorem pureTransform_flat_of_generatorCharts
    (hC : Ideal.span (Set.range (fun i => (C i).val)) = I)
    (hflat : ∀ i, letI : Algebra R (BlowupChartRing I (C i)) :=
        (chartBaseMap I (C i)).toAlgebra
      Module.Flat (BlowupChartRing I (C i))
        (modulePureTransform (chartBaseMap I (C i) f) (BlowupChartRing I (C i) ⊗[R] M)))
    (a : I) :
    letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
    Module.Flat (BlowupChartRing I a)
      (modulePureTransform (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M)) := by
  let A := BlowupChartRing I a
  let D (i : ι) := BlowupOverlapRing I a (C i)
  let : Algebra R A := (chartBaseMap I a).toAlgebra
  let (i : ι) : Algebra R (D i) :=
    ((chartOverlapFromLeft I a (C i)).comp (chartBaseMap I a)).toAlgebra
  let : SMul R A := (inferInstance : Algebra R A).toSMul
  let (i : ι) : SMul R (D i) := (inferInstance : Algebra R (D i)).toSMul
  let (i : ι) : Algebra A (D i) := (chartOverlapFromLeft I a (C i)).toAlgebra
  have (i : ι) : IsScalarTower R A (D i) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have (i : ι) : IsLocalization.Away (chartRatio I a (C i)) (D i) :=
    chartOverlap_isLocalizationLeft I a (C i)
  let N (i : ι) := modulePureTransform
    (chartOverlapFromLeft I a (C i) (chartBaseMap I a f)) (D i ⊗[R] M)
  have (i : ι) : Module.Flat (D i) (N i) :=
    chartOverlapPureTransform_flat_from_right I a (C i) f M (hflat i)
  have (i : ι) : Module.Flat A (D i) :=
    IsLocalization.flat (D i) (Submonoid.powers (chartRatio I a (C i)))
  have (i : ι) : Module.Flat A (N i) := Module.Flat.trans A (D i) (N i)
  let η (i : ι) : modulePureTransform (chartBaseMap I a f) (A ⊗[R] M) →ₗ[A] N i :=
    tensorPureTransformLocalizationMap R A (D i) M (chartBaseMap I a f)
  have (i : ι) : IsLocalizedModule.Away (chartRatio I a (C i)) (η i) :=
    inferInstanceAs (IsLocalizedModule.Away (chartRatio I a (C i))
      (tensorPureTransformLocalizationMap R A (D i) M (chartBaseMap I a f)))
  exact flat_of_isLocalized_family_span (fun i => chartRatio I a (C i))
    (span_chartRatio_generators_eq_top I a C hC) N η

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas

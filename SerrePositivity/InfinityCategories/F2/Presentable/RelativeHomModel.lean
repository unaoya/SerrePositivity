module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeHomCosliceEquivalence
public import SerrePositivity.InfinityCategories.F2.Compact.RepresentableCoslice
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseUnstraightening

/-!
概要：相対豊穣 Hom の全関手を、N の定義に使う元の大きい共変 Hom と比較する。
方針：元の coslice 比較の全空間同値を分類し、同じ小さい Hom 図式の宇宙変更へ移す。
規約：元の対象・全射・高次の整合性を保持。値ごとの比較を全自然同型の代わりに使わない。
使われ方：小さい空間の compact 性と前層の compact 生成圏への宇宙比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の大きい共変 Hom は、同じ相対豊穣 Hom の全関手を宇宙変更したものと全自然同型。 -/
def relativeHom_covariantModelIso {B : SSet.{u}} (q : LeftFibrationObject B) :
    FunctorIso (covariantRepresentableInfinity (C := LeftFibrationInfinity B)
      (coherentNerveVertex q))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (leftFibrationCoherentEvaluation q.val) ≫
        Compact.spaceUniverseDiagram.{u}) :=
  Compact.covariantRepresentableInfinity_cosliceIso (coherentNerveVertex q) ≪≫
    Compact.leftClassification_of_precompositionEquivalence
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex q)))
      (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
      (relativeHomCosliceComparison q) (relativeHomCosliceComparison_projection q)
      (relativeHomCosliceComparison_isQCatEquivalence q).isPrecompositionEquivalence ≪≫
    Compact.spaceUniverseUnstraightening_classificationIso (leftFibrationCoherentEvaluation q.val)

end SerrePositivity.InfinityCategories.F2.Presentable

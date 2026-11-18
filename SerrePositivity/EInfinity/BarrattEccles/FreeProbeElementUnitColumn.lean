module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeElementColumnProperties
/-! 概要：元の要素圏上で自由随伴単位の全自然変換と二つの正方形を構成する。
方針：同じ単位の自然性と保存済みの全成分公式を使う。
規約：元の列・augmentation・評価・同じ標的の半自由置換を保持する。
使われ方：標準導来単位比較の全関手圏の三角形。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A] (X : Complex A) (B : (operad A).Algebra)

/-- 概要：同じ要素圏の複体列から自由列の底への元の単位。
方針：各実 tensor 対象に同じ随伴単位を適用する。
規約：全射に自然。使われ方：二つの全族正方形の共通辺。 -/
def freeProbeElementUnitColumn :
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val ⟶
    freeProbeElementColumn A X B ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A) where
  app s := (operad A).freeAlgebraAdjunction.unit.app
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val).obj s)
  naturality _ _ f := (operad A).freeAlgebraAdjunction.unit.naturality
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val).map f)

/-- 概要：元の全 augmentation と単位の自然変換正方形。
方針：保存済みの元の全成分公式を自然変換等式へ戻す。
規約：全要素圏を保持。使われ方：全 roof の左脚比較。 -/
lemma freeProbeElementUnitColumn_augmentation :
    freeProbeElementUnitColumn A X B ≫
      Functor.whiskerRight (freeProbeElementColumnAugmentation A X B)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)) =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementAugmentation A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val ≫
      (Functor.const (freeProbeElementIndex A X B)).map
        ((operad A).freeAlgebraAdjunction.unit.app
          ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)) := by
  apply NatTrans.ext
  funext s
  exact freeProbeElementColumnAugmentation_unit A X B s

/-- 概要：元の全評価と単位の自然変換正方形。
方針：同じ評価成分の随伴公式を全列へ束ねる。
規約：同じ半自由 augmentation を保持。使われ方：全 roof の右脚比較。 -/
lemma freeProbeElementUnitColumn_evaluation :
    freeProbeElementUnitColumn A X B ≫
      Functor.whiskerRight (freeProbeElementColumnEvaluation A X B)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget (operad A)) =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X)
      (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValue A B.carrier).val ≫
      (Functor.const (freeProbeElementIndex A X B)).map
        (_root_.SerrePositivity.ComplexLimits.complexSemifreeResolutionValueAugmentation A B.carrier) := by
  apply NatTrans.ext
  funext s
  exact freeProbeElementColumnEvaluation_unit A X B s

end SerrePositivity.EInfinity.BarrattEccles

module
public import SerrePositivity.EInfinity.Modules.TensorFrameOriginalAugmentation
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementEvaluationIndex

/-!
概要：同じ全要素図式の評価同型は、元の二つの augmentation を結ぶ。
方針：全 frame における元の実射の可換式を各要素で使う。
規約：HA 1.3.1.13、同じ余単位と同じ全図式。
使われ方：M10 の元の全評価屋根の両脚を複体側へ比較する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：同じ全図式の評価同型は元の augmentation 自然変換と可換。
方針：定値関手の同型も保持し、元の frame の可換式を適用する。
規約：HA 1.3.1.13、全射。使われ方：同じ実屋根の左脚の比較。 -/
lemma strictRawModuleTensorElementEvaluationDiagramIso_augmentation
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    (strictRawModuleTensorElementEvaluationDiagramIso A X P Q x).hom ≫
      CategoryTheory.Functor.whiskerRight
        (strictRawModuleTensorElementAugmentation A X P Q) (moduleEvaluation A _ x) ≫
      (Functor.constComp (strictRawModuleTensorElementIndex A X P Q)
        ((strictRawModuleProbeFunctor A X).obj P) (moduleEvaluation A _ x)).hom =
      CategoryTheory.Functor.whiskerLeft
        (strictRawModuleTensorElementEvaluationIndex A X P Q x)
        (normalizedTensorElementAugmentation A
          ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
          ((moduleEvaluation A _ x).obj Q)) := by
  apply NatTrans.ext
  funext s
  simp only [NatTrans.comp_app, Functor.constComp_hom_app, Category.comp_id]
  exact moduleTensorEvaluationFrameIso_original_augmentation A _
    ((strictRawModuleProbeFunctor A X).obj P) x _

end SerrePositivity.EInfinity.BarrattEccles

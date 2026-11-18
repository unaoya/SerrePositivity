module
public import SerrePositivity.EInfinity.Modules.TensorFrameEvaluation
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementDiagram
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementDiagram

/-!
概要：元の全加群 frame の要素図式を、対象ごとの複体の要素図式に送る。
方針：全 Hom 評価の要素圏関手と同じ符号付き frame 同型を使う。
規約：HA 1.3.1.13、全射・全単体作用素・元の評価射を保持。
使われ方：M10 の全三相データの対象と評価係数の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
attribute [local instance] uliftCategory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：元の全要素圏を同じ対象での複体の全要素圏へ送る。
方針：同じ全 Hom 評価に要素圏関手を作用させる。
規約：HA 1.3.1.13、全次数。使われ方：全三角形の評価。 -/
def strictRawModuleTensorElementEvaluationIndex
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    strictRawModuleTensorElementIndex A X P Q ⥤
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A
        ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
        ((moduleEvaluation A _ x).obj Q) :=
  ULiftHom.down ⋙ ULift.downFunctor ⋙
    (moduleTensorEvaluationHomMap A _ ((strictRawModuleProbeFunctor A X).obj P) Q x).mapElements.op ⋙
    ULift.upFunctor ⋙ ULiftHom.up

/-- 概要：元の全要素図式の評価は同じ複体要素図式に自然に同型。
方針：同じ次数射影に符号付き frame 同型を前合成する。
規約：HA 1.3.1.13、全射。使われ方：元の中間対象表示の移送。 -/
def strictRawModuleTensorElementEvaluationDiagramIso
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    strictRawModuleTensorElementEvaluationIndex A X P Q x ⋙
      _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDiagram A
        ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
        ((moduleEvaluation A _ x).obj Q) ≅
      strictRawModuleTensorElementDiagram A X P Q ⋙ moduleEvaluation A _ x :=
  CategoryTheory.Functor.isoWhiskerLeft (strictRawModuleTensorElementDegree A X P Q)
    (moduleTensorEvaluationFrameIso A _ ((strictRawModuleProbeFunctor A X).obj P) x)

/-- 概要：全要素図式の同型は元の二つの実評価自然変換を結ぶ。
方針：全 Hom 評価の元の値を各要素で使う。
規約：HA 1.3.1.13、全射の可換性。使われ方：全評価三角形の比較。 -/
lemma strictRawModuleTensorElementEvaluationDiagramIso_evaluation
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    (strictRawModuleTensorElementEvaluationDiagramIso A X P Q x).hom ≫
      CategoryTheory.Functor.whiskerRight
        (strictRawModuleTensorElementEvaluation A X P Q) (moduleEvaluation A _ x) ≫
      (Functor.constComp (strictRawModuleTensorElementIndex A X P Q) Q
        (moduleEvaluation A _ x)).hom =
      CategoryTheory.Functor.whiskerLeft
        (strictRawModuleTensorElementEvaluationIndex A X P Q x)
        (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementEvaluation A
          ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
          ((moduleEvaluation A _ x).obj Q)) := by
  apply NatTrans.ext
  funext s
  simp only [NatTrans.comp_app, Functor.constComp_hom_app, Category.comp_id]
  exact (moduleTensorEvaluationHomMap_frame A _
    ((strictRawModuleProbeFunctor A X).obj P) Q x _
      ((strictRawModuleTensorElementEvaluation A X P Q).app s)).symm

end SerrePositivity.EInfinity.BarrattEccles

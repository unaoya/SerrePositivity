module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementParameter
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementEvaluationIndex
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementParameter

/-!
概要：元の全要素圏の終端パラメータ族と各対象での frame Hom 評価は可換。
方針：同じ要素圏関手を nerve に送り、全 Hom 評価の全作用素自然性を使う。
規約：HA 1.3.1.13、元の全単体・全次数・全退化。
使われ方：M10 の元の大域 pinched 族の評価比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：元の BE の全 frame Hom と同じ表示の全評価写像。
方針：検証済みの加群 frame 評価の始域表示を明示する。
規約：HA 1.3.1.13、同じ射。使われ方：Hom end の表示の照合。 -/
def strictRawModuleTensorEvaluationHomMap
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    (((strictRawModuleProbeTensorHom A X).obj (op P)).obj Q) ⟶
      (cosimplicialHom (normalizedSimplexTensor A
        ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P)))).obj
        ((moduleEvaluation A _ x).obj Q) :=
  moduleTensorEvaluationHomMap A _ ((strictRawModuleProbeFunctor A X).obj P) Q x

/-- 概要：元の全要素圏の評価関手を同じ全 nerve の写像にする。
方針：全単体列に元の関手を後合成する。
規約：HA 1.3.1.13、宇宙の表示を明示。使われ方：大域族の全評価。 -/
def strictRawModuleTensorElementEvaluationIndexNerveMap
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
      nerve (normalizedTensorElementIndex A
        ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
        ((moduleEvaluation A _ x).obj Q)) where
  app _ := ↾fun c => c ⋙ strictRawModuleTensorElementEvaluationIndex A X P Q x
  naturality _ _ _ := rfl

private lemma sset_naturality_apply {F G : SSet.{u}} (α : F ⟶ G)
    {n m : SimplexCategory} (θ : n ⟶ m) (g : F.obj (op m)) :
    α.app (op n) (F.map θ.op g) = G.map θ.op (α.app (op m) g) :=
  ConcreteCategory.congr_hom (α.naturality θ.op) g

/-- 概要：元の全終端パラメータの族は同じ全 Hom 評価と可換。
方針：同じ終端作用素における自然性を元の最終評価射で評価する。
規約：HA 1.3.1.13、全単体。使われ方：元の全 pinched 族の比較。 -/
lemma strictRawModuleTensorElementParameterMap_evaluation
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    strictRawModuleTensorElementParameterMap A X P Q ≫
      SSet.uliftFunctor.{u + 1, u}.map
        (strictRawModuleTensorEvaluationHomMap A X P Q x) =
    strictRawModuleTensorElementEvaluationIndexNerveMap A X P Q x ≫
      normalizedTensorElementParameterMap A
        ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
        ((moduleEvaluation A _ x).obj Q) := by
  apply NatTrans.ext
  funext d
  rcases d with ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro c
  let α := strictRawModuleTensorEvaluationHomMap A X P Q x
  let θ := strictRawModuleTensorElementTerminalParameter A X P Q c
  let g := (strictRawModuleTensorElementEvaluation A X P Q).app (c.obj (Fin.last n))
  change ULift.up (α.app (op ⦋n⦌)
      (((strictRawModuleProbeTensorFrame A X).obj P).map θ ≫ g)) =
    ULift.up ((normalizedSimplexTensor A
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))).map θ ≫
        α.app (op ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n)))) g)
  exact congrArg (ULift.up : _ → ULift.{u + 1} _)
    (sset_naturality_apply α θ g)

end SerrePositivity.EInfinity.BarrattEccles

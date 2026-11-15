module
public import SerrePositivity.EInfinity.Modules.TensorPinchedEvaluation
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementParameterEvaluation

/-!
概要：元の大域 pinched 族全体の評価は複体側の元の大域族と一致する。
方針：同じ終端パラメータの全自然性と元の pinched 座標の全評価式を合成する。
規約：HA 1.3.1.13、全パラメータ・全単体。
使われ方：M10 の実三相データの pinched 成分の全評価比較。
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
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：元の全 pinched 族を Hom end で評価すると同じ複体側の全族。
方針：同じ全終端パラメータと座標同型の自然性を貼り合わせる。
規約：HA 1.3.1.13、実写像の等式。使われ方：全三相 pinched 成分の比較。 -/
lemma strictRawModuleTensorElementPinchedMap_evaluation
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    strictRawModuleTensorElementPinchedMap A X P Q ≫
      pinchedHomChainMap (moduleHomπ A _
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
        (ForgetEnrichment.to (Complex A) Q) x) =
    strictRawModuleTensorElementEvaluationIndexNerveMap A X P Q x ≫
      normalizedTensorElementPinchedMap A
        ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
        ((moduleEvaluation A _ x).obj Q) := by
  have h := moduleTensorHomPinchedIso_evaluation A _
    ((strictRawModuleProbeFunctor A X).obj P) Q x
  have hp := congrArg (fun f => strictRawModuleTensorElementParameterMap A X P Q ≫ f) h
  calc
    _ = strictRawModuleTensorElementParameterMap A X P Q ≫
      (SSet.uliftFunctor.{u + 1, u}.map
        (strictRawModuleTensorEvaluationHomMap A X P Q x) ≫
        (normalizedTensorPinchedIso A
          ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
          ((moduleEvaluation A _ x).obj Q)).hom) := by
      exact hp.symm
    _ = _ := by
      rw [← Category.assoc, strictRawModuleTensorElementParameterMap_evaluation]
      rfl

end SerrePositivity.EInfinity.BarrattEccles

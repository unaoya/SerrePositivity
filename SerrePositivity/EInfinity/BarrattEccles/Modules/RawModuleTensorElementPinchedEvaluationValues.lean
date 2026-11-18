module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementPinchedEvaluationMap

/-!
概要：元の大域 pinched 族の全評価等式から、実単体と全線形成分の評価を回収する。
方針：元の全写像の等式を単体で評価し、同じ線形表示に送る。
規約：HA 1.3.1.13、全次数・全有限部分集合。
使われ方：M10 の元の実三相データの pinched 成分の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：元の全族の各実 pinched 単体の評価は複体側の同じ実単体。
方針：元の全写像の等式を評価する。
規約：HA 1.3.1.13、全次元。使われ方：全 cochain の比較。 -/
lemma strictRawModuleTensorElementPinchedMap_evaluation_app {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    pinchedHomChainMapSimplex (moduleHomπ A _
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) Q) x)
      ((strictRawModuleTensorElementPinchedMap A X P Q).app (op ⦋n⦌) c) =
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q)).app (op ⦋n⦌)
      (c ⋙ strictRawModuleTensorElementEvaluationIndex A X P Q x) := by
  exact congrArg (fun f : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    PinchedHom.pinchedHom A (Complex A)
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q) => f.app (op ⦋n⦌) c)
    (strictRawModuleTensorElementPinchedMap_evaluation A X P Q x)

/-- 概要：同じ実単体の全線形表示の評価も同じ複体側の全線形表示。
方針：同じ座標の自然性と実単体の等式を合成する。
規約：HA 1.3.1.13、全係数。使われ方：三相 pinched 成分の比較。 -/
lemma strictRawModuleTensorElementPinchedMap_linear_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    pinchedLinearSimplexMap (moduleHomπ A _
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) Q) x)
      (PinchedHom.toLinearSimplex
        ((strictRawModuleTensorElementPinchedMap A X P Q).app (op ⦋n⦌) c)) =
    PinchedHom.toLinearSimplex ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q)).app (op ⦋n⦌)
      (c ⋙ strictRawModuleTensorElementEvaluationIndex A X P Q x)) :=
  (pinchedHomChainMapSimplex_linear _ _).symm.trans
    (congrArg PinchedHom.toLinearSimplex
      (strictRawModuleTensorElementPinchedMap_evaluation_app A X P Q c x))

end SerrePositivity.EInfinity.BarrattEccles

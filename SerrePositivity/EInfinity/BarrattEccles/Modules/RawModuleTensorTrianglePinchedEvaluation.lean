module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorElementPinchedEvaluationValues
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorTrianglePieces
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorTrianglePieces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGWalkingHomPinchedGeneral

/-!
概要：元の pinched 実単体と三相引き戻しの dg 評価は複体側の指定実データと一致。
方針：既存の dg 関手と Hom 鎖写像の実単体の照合、全引き戻し自然性を使う。
規約：HA 1.3.1.6・1.3.1.13、全 cochain と退化を保持。
使われ方：M10 の元の三相データの pinched 分岐の全評価。
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
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：元の pinched 実単体の dg 評価は複体側の同じ実単体。
方針：元の全 Hom 鎖写像の作用を同じ dg 関手の作用へ戻す。
規約：HA 1.3.1.13、全単体。使われ方：三相の実データの比較。 -/
lemma strictRawModuleTensorElementPinchedMap_simplex_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    ((strictRawModuleTensorElementPinchedMap A X P Q).app (op ⦋n⦌) c).val.map
      (moduleEvaluationDG A _ x) =
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementPinchedMap A
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q)).app (op ⦋n⦌)
      (c ⋙ strictRawModuleTensorElementEvaluationIndex A X P Q x)).val :=
  (dgFunctorPinchedChainMap_val A (moduleEvaluationDG A _ x) _).symm.trans
    (congrArg (fun s : (PinchedHom.pinchedHom A (Complex A)
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q)) _⦋n⦌ => s.val)
      (strictRawModuleTensorElementPinchedMap_evaluation_app A X P Q c x))

/-- 概要：三相の元の pinched 分岐の全 dg データの評価は指定複体側と一致。
方針：同じ実単体の評価と任意単調作用素の引き戻し自然性を合成する。
規約：HA 1.3.1.6、全有限部分集合・次数。使われ方：全 HA 方程式の比較。 -/
lemma strictRawModuleTensorTrianglePinched_evaluation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (τ : Fin (n + 1) →o Fin 3)
    (x : dgAlgebraCategory A ((assocForget A).obj X)) :
    (strictRawModuleTensorTrianglePinched A X P Q c τ).toSimplexData.map
      (moduleEvaluationDG A _ x) =
    (_root_.SerrePositivity.ComplexLimits.normalizedTensorTrianglePinched A
      ((moduleEvaluation A _ x).obj ((strictRawModuleProbeFunctor A X).obj P))
      ((moduleEvaluation A _ x).obj Q)
      (c ⋙ strictRawModuleTensorElementEvaluationIndex A X P Q x) τ).toSimplexData :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map_pullback
    ((strictRawModuleTensorElementPinchedMap A X P Q).app (op ⦋n⦌) c).val.toSimplexData
    (moduleEvaluationDG A _ x) (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ)).trans
      (congrArg (fun s : Simplex A (Complex A) (n + 1) =>
        s.toSimplexData.pullback (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ))
        (strictRawModuleTensorElementPinchedMap_simplex_evaluation A X P Q c x))

end SerrePositivity.EInfinity.BarrattEccles

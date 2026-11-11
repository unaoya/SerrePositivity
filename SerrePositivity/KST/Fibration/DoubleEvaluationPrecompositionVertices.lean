module
public import SerrePositivity.KST.Fibration.DoubleEvaluationPrecomposition
public import SerrePositivity.KST.Fibration.StraighteningBaseChangeTranspose

/-! # 同じ指定頂点の像を保つ前合成は、二重評価の頂点と成分を保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 前合成の元の頂点像を指定すると、同じ二重評価の頂点を回収する。 -/
theorem doubleFunctorEvaluation_precomp_vertex_of_eq {K L A Y : SSet.{u}}
    (F : K ⟶ (ihom A).obj Y) (q : L ⟶ K) (l : L _⦋0⦌) (a : A _⦋0⦌)
    (x : K _⦋0⦌) (hx : q.app (Opposite.op ⦋0⦌) l = x) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.doubleFunctorEvaluation (Y := Y) l a).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (q ≫ F)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.doubleFunctorEvaluation (Y := Y) x a).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) := by
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Straightening.doubleFunctorEvaluation_precomp_vertex F q l a).symm.trans
    (congrArg (fun z : K _⦋0⦌ => (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.doubleFunctorEvaluation (Y := Y) z a).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) hx)

/-- 同じ指定頂点像を保つ前合成同型は、同じ二重成分を保持する。 -/
theorem functorIso_pre_doubleMap_of_vertex {K L A Y : SSet.{u}}
    {F G : K ⟶ (ihom A).obj Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) (q : L ⟶ K)
    (l : L _⦋0⦌) (a : A _⦋0⦌) (x : K _⦋0⦌)
    (hx : q.app (Opposite.op ⦋0⦌) l = x) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (e.precomp q) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.doubleFunctorEvaluation (Y := Y) l a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.doubleFunctorEvaluation (Y := Y) x a)) := by
  exact (functorIso_pre_doubleMap e q l a).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.vertexIso_map_heq e (congrArg (fun z : K _⦋0⦌ =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.doubleFunctorEvaluation (Y := Y) z a) hx))

end SerrePositivity.KST.Fibration

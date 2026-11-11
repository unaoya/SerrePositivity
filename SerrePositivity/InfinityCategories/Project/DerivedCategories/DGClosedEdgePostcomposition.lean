module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
/-!
概要：dg 関手と実後続関手による閉辺の像の可逆性を、同じ閉射の像で計算する。
方針：dg 関手による実閉辺の全一次単体等式に、後続関手を適用する。
規約：両端の表示輸送を保つ。使われ方：K-flat 入力上の通常 kernel tensor。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
/-- 閉辺の dg 像を元の実辺へ同定した後で、任意の後続関手による可逆性を計算する。 -/
lemma dgClosedEdge_postcomposition_isInvertible_iff (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
    {Y : SSet.{max u v}} (q : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E ⟶ Y)
    {M N : _root_.SerrePositivity.DifferentialGraded.ClosedCategory R C} (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R C f).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F ≫ q))) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge R E (F.onClosed.map f)).edge).map
          ((truncation 2).map q)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := Y)
  exact congrArg (fun t => q.app (Opposite.op ⦋1⦌) t) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_map R C F f)
end SerrePositivity.InfinityCategories.Project.DerivedCategories

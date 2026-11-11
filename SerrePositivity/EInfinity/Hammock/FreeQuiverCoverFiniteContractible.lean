module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverFiniteHull
public import SerrePositivity.EInfinity.Hammock.QuiverTreeFiniteWeakMaps

/-!
# 元の根付き被覆の有限包の実際の hammock の可縮性

概要：任意の元の有限頂点集合の根に閉じた包の全 hammock は弱可縮となる。
方針：証明済みの元の測地木と自由 groupoid の薄さへ有限帰納を代入する。
規約：木性や可縮性を追加入力にせず、元の被覆の生成辺を保持する。
使われ方：全被覆の固定端点の成分の可縮性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory SerrePositivity.InfinityCategories

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma finiteHull_colimit_isWeaklyContractible (S : Finset (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull A S)
    ∀ x y : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull A S)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph
        (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull A S)))) x y) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoid_isThin A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull A S)
  exact QuiverTree.finite_colimit_isWeaklyContractible (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull A S)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull_closed A S)

lemma finiteHull_subset_colimitMap_isWeakHomotopyEquivalence
    {S R : Finset (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)} (h : S ⊆ R) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull A S)
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull A R)
    ∀ x y : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull A S)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subsetRelative (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull_mono A h)) x y) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTreeArborescence A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoid_isThin A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull A S)
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull A R)
  exact QuiverTree.subset_colimitMap_isWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.spanningTree A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull_closed A S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull_closed A R) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.finiteHull_mono A h)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover

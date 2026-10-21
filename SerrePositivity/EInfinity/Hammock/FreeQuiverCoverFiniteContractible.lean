module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverFiniteHull
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

lemma finiteHull_colimit_isWeaklyContractible (S : Finset (Vertex A)) :
    letI := quiver A
    letI := FiniteQuiver.quiver (finiteHull A S)
    ∀ x y : Paths (FiniteQuiver.Vertex (finiteHull A S)),
      IsWeaklyContractible (colimitGraph
        (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex (finiteHull A S)))) x y) := by
  let := quiver A
  let := spanningTreeArborescence A
  let := groupoid_isThin A
  let := FiniteQuiver.quiver (finiteHull A S)
  exact QuiverTree.finite_colimit_isWeaklyContractible (spanningTree A) (finiteHull A S)
    (finiteHull_closed A S)

lemma finiteHull_subset_colimitMap_isWeakHomotopyEquivalence
    {S R : Finset (Vertex A)} (h : S ⊆ R) :
    letI := quiver A
    letI := FiniteQuiver.quiver (finiteHull A S)
    letI := FiniteQuiver.quiver (finiteHull A R)
    ∀ x y : Paths (FiniteQuiver.Vertex (finiteHull A S)),
      IsWeakHomotopyEquivalence (Relative.colimitMap
        (FiniteQuiver.subsetRelative (finiteHull_mono A h)) x y) := by
  let := quiver A
  let := spanningTreeArborescence A
  let := groupoid_isThin A
  let := FiniteQuiver.quiver (finiteHull A S)
  let := FiniteQuiver.quiver (finiteHull A R)
  exact QuiverTree.subset_colimitMap_isWeakHomotopyEquivalence (spanningTree A)
    (finiteHull_closed A S) (finiteHull_closed A R) (finiteHull_mono A h)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover

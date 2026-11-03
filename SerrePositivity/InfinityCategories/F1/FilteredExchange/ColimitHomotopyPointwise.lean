module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Core.HomotopyNatTrans
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1.ColimitHomotopyInvertible
public import SerrePositivity.InfinityCategories.Core.HomotopyInvertibility
public import SerrePositivity.InfinityCategories.Core.HomotopyPrecomposition

/-!
概要：元の余極限余錐の比較は基底の各点で可逆なら指定頂点でも可逆。
方針：制限したホモトピーの各辺を照合し、普遍余錐間の可逆性の反映を使う。
規約：元の全ホモトピーを保持。使われ方：単体形状の coherent filtered 極限交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 制限後の頂点上の比較辺は、元のホモトピーの像の頂点上の辺と一致。 -/
lemma homotopyVertexEdge_precomp {A B X : SSet.{u}} (i : A ⟶ B)
    {F G : B ⟶ X} (H : SSet.Homotopy F G) (a : A _⦋0⦌) :
    (simplicialHomotopyVertexEdge (stableHomotopyPrecomp i H) a).edge =
      (simplicialHomotopyVertexEdge H (i.app (Opposite.op ⦋0⦌) a)).edge := by
  change H.h.app (Opposite.op ⦋1⦌)
      (i.app (Opposite.op ⦋1⦌) (SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge,
        homotopyIntervalEdge.edge) = _
  have hi := congrArg SSet.Truncated.Edge.edge
    (SSet.Truncated.Edge.map_id (X := (truncation 2).obj A) a ((truncation 2).map i))
  change i.app (Opposite.op ⦋1⦌) (SSet.Truncated.Edge.id (X := (truncation 2).obj A) a).edge =
    (SSet.Truncated.Edge.id (X := (truncation 2).obj B)
      (i.app (Opposite.op ⦋0⦌) a)).edge at hi
  rw [hi]
  rfl

/-- 元の二つの普遍余錐間の比較は、基底の各点で可逆なら全体でも可逆。 -/
lemma colimitHomotopy_isInvertible_of_pointwise {J X : SSet.{u}} [Quasicategory X]
    {p q : J ⟶ X} (c : JoinCocone p) (d : JoinCocone q)
    (hc : IsColimitCone c) (hd : IsColimitCone d) (H : SSet.Homotopy c.val d.val)
    (hH : ∀ j : J _⦋0⦌, IsInvertibleEdge (simplicialHomotopyVertexEdge H
      ((joinInl J Δ[0]).app (Opposite.op ⦋0⦌) j)).toTruncated) :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy H) := by
  apply colimitCoconeHomotopy_isInvertible_of_precomp c d hc hd H
  apply functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
  intro j
  exact (isInvertibleEdge_congr (homotopyVertexEdge_precomp (joinInl J Δ[0]) H j)).mpr
    (hH j)

/-- 元の余極限頂点での指定比較辺は、基底の各点で可逆な比較から可逆となる。 -/
lemma colimitHomotopy_vertex_isInvertible {J X : SSet.{u}} [Quasicategory X]
    {p q : J ⟶ X} (c : JoinCocone p) (d : JoinCocone q)
    (hc : IsColimitCone c) (hd : IsColimitCone d) (H : SSet.Homotopy c.val d.val)
    (hH : ∀ j : J _⦋0⦌, IsInvertibleEdge (simplicialHomotopyVertexEdge H
      ((joinInl J Δ[0]).app (Opposite.op ⦋0⦌) j)).toTruncated) :
    IsInvertibleEdge (simplicialHomotopyVertexEdge H
      ((joinInr J Δ[0]).app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv (𝟙 Δ[0])))).toTruncated :=
  homotopyVertex_isInvertible_of_functorEdge H
    (colimitHomotopy_isInvertible_of_pointwise c d hc hd H hH) _

end SerrePositivity.InfinityCategories.F2

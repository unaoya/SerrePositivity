module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverGroupoidConnected
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.QuiverTreeExhaustion

/-!
# 元の根付き被覆の全生成辺を含む測地木

概要：根付き被覆の各生成辺は測地木に正または逆向きで属する。
方針：実際の根からの連結性と自由 groupoid の薄さを代入する。
規約：木性を仮定に追加せず、元の被覆の全生成辺に結論を適用する。
使われ方：有限部分木の葉の除去と全指定 hammock の成分。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma rootedSymmetricConnected :
    letI := quiver A
    Quiver.RootedConnected (Quiver.Symmetrify.of.obj (root A)) := by
  let := quiver A
  exact ⟨root_connected A⟩

def spanningTree : letI := quiver A; WideSubquiver (Quiver.Symmetrify (Vertex A)) := by
  letI := quiver A
  letI := rootedSymmetricConnected A
  exact Quiver.geodesicSubtree (Quiver.Symmetrify.of.obj (root A))

@[instance_reducible] def spanningTreeArborescence :
    letI := quiver A
    Quiver.Arborescence (spanningTree A) := by
  letI := quiver A
  letI := rootedSymmetricConnected A
  exact Quiver.geodesicArborescence (Quiver.Symmetrify.of.obj (root A))

lemma every_edge_in_spanningTree :
    letI := quiver A
    ∀ {x y : Vertex A} (f : x ⟶ y),
      f.toPos ∈ spanningTree A x y ∨ f.toNeg ∈ spanningTree A y x := by
  let := quiver A
  let := spanningTreeArborescence A
  let := groupoid_isThin A
  intro x y f
  exact QuiverTree.every_edge_in_tree (spanningTree A) f

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover

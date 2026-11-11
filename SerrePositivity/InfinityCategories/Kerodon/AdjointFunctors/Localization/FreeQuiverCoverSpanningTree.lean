module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverGroupoidConnected
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeExhaustion

/-!
# 元の根付き被覆の全生成辺を含む測地木

概要：根付き被覆の各生成辺は測地木に正または逆向きで属する。
方針：実際の根からの連結性と自由 groupoid の薄さを代入する。
規約：木性を仮定に追加せず、元の被覆の全生成辺に結論を適用する。
使われ方：有限部分木の葉の除去と全指定 hammock の成分。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma rootedSymmetricConnected :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Quiver.RootedConnected (Quiver.Symmetrify.of.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A)) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.root_connected A⟩

def spanningTree : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A; WideSubquiver (Quiver.Symmetrify (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  letI := rootedSymmetricConnected A
  exact Quiver.geodesicSubtree (Quiver.Symmetrify.of.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A))

@[instance_reducible] def spanningTreeArborescence :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Quiver.Arborescence (spanningTree A) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  letI := rootedSymmetricConnected A
  exact Quiver.geodesicArborescence (Quiver.Symmetrify.of.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A))

lemma every_edge_in_spanningTree :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A} (f : x ⟶ y),
      f.toPos ∈ spanningTree A x y ∨ f.toNeg ∈ spanningTree A y x := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := spanningTreeArborescence A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoid_isThin A
  intro x y f
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.every_edge_in_tree (spanningTree A) f

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

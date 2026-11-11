module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverCostars

/-!
# 元の根付き被覆の全射列の一意な持ち上げ

概要：元の有向射列と対称化した射列は指定した始点から一意に持ち上がる。
方針：元の被覆性を Mathlib の射列の持ち上げと対称化の被覆性へ適用する。
規約：元の射列と実際の持ち上げ終点を保持する。
使われ方：元の hammock の全行と全縦射を持ち上げる。

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

def pathStarEquiv (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Quiver.PathStar x ≃ Quiver.PathStar x.base := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact Equiv.ofBijective ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).pathStar x)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverCostars.projection_isCovering A).pathStar_bijective x)

lemma symmetrify_isCovering :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).symmetrify.IsCovering := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverCostars.projection_isCovering A).symmetrify

def symmetricPathStarEquiv (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Quiver.PathStar (Quiver.Symmetrify.of.obj x) ≃
      Quiver.PathStar (Quiver.Symmetrify.of.obj x.base) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact Equiv.ofBijective ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).symmetrify.pathStar (Quiver.Symmetrify.of.obj x))
    ((symmetrify_isCovering A).pathStar_bijective _)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

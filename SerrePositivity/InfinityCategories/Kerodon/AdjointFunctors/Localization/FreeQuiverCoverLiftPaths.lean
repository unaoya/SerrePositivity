module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverPositivePaths

/-!
# 元の基底射列の指定始点からの持ち上げと全データの一意性

概要：元の射列を持ち上げ、その基底射列・持ち上げ終点・全射列を回収する。
方針：元の pathStar の全単射を使う。
規約：基底の射列の像だけでなく実際の持ち上げ全体を扱う。
使われ方：元の hammock の行と縦射の同時持ち上げ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftPaths
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def liftPath (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) {B : Q} (p : Quiver.Path x.base B) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Quiver.PathStar x := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathStarEquiv A x).symm ⟨B, p⟩

lemma liftPath_projection (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) {B : Q} (p : Quiver.Path x.base B) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).pathStar x (liftPath A x p) = ⟨B, p⟩ := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathStarEquiv A x).apply_symm_apply ⟨B, p⟩

lemma lifted_pathStar_unique (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ p q : Quiver.PathStar x,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).pathStar x p = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).pathStar x q → p = q := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathStarEquiv A x).injective

lemma liftPath_unique (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) {B : Q} (p : Quiver.Path x.base B) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ q : Quiver.PathStar x, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).pathStar x q = ⟨B, p⟩ → q = liftPath A x p := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro q hq
  exact lifted_pathStar_unique A x q (liftPath A x p) (hq.trans (liftPath_projection A x p).symm)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftPaths

module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverStars

/-!
# 元の根付き quiver の costar の持ち上げ

概要：指定した持ち上げ頂点へ入る元の矢も一意に持ち上がる。
方針：元の groupoid の逆射による右合成と元の逆射の法則を使う。
規約：元の基底矢と持ち上げ始点そのものを回収する。
使われ方：元の quiver の被覆性と対称化の一意な持ち上げ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverCostars
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

def backwardSource (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) {B : Q} (f : B ⟶ x.base) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A :=
  ⟨B, x.path ≫ inv ((Quiver.FreeGroupoid.of Q).map f)⟩

def backwardArrow (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) {B : Q} (f : B ⟶ x.base) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    backwardSource A x f ⟶ x := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact ⟨f, by simp only [backwardSource, Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩

def costarEquiv (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Quiver.Costar x ≃ Quiver.Costar x.base := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact
    { toFun := fun s => ⟨s.1.base, s.2.val⟩
      invFun := fun s => ⟨backwardSource A x s.2, backwardArrow A x s.2⟩
      left_inv := by
        rintro ⟨⟨B, p⟩, ⟨f, hf⟩⟩
        change B ⟶ x.base at f
        change p ≫ (Quiver.FreeGroupoid.of Q).map f = x.path at hf
        have he := congrArg (fun q => q ≫ inv ((Quiver.FreeGroupoid.of Q).map f)) hf
        have hp : p = x.path ≫ inv ((Quiver.FreeGroupoid.of Q).map f) := by
          simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using he
        subst p
        rfl
      right_inv := by
        rintro ⟨B, f⟩
        rfl }

lemma projection_isCovering : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A; (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).IsCovering := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.star_bijective A, fun x => (costarEquiv A x).bijective⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverCostars

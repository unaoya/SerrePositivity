module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover

/-!
# 元の根付き quiver の star の持ち上げ

概要：指定した持ち上げ頂点から出る元の矢は一意に持ち上がる。
方針：元の groupoid の矢の右合成で終点を作り、元の終点の等式から一意性を得る。
規約：元の基底矢と持ち上げ終点そのものを回収する。
使われ方：元の quiver の被覆性と全射列の一意な持ち上げ。

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

def starEquiv (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Quiver.Star x ≃ Quiver.Star x.base := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact
    { toFun := fun s => ⟨s.1.base, s.2.val⟩
      invFun := fun s => ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.forwardTarget A x s.2, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.forwardArrow A x s.2⟩
      left_inv := by
        rintro ⟨⟨B, p⟩, ⟨f, hf⟩⟩
        change x.base ⟶ B at f
        change x.path ≫ (Quiver.FreeGroupoid.of Q).map f = p at hf
        subst p
        rfl
      right_inv := by
        rintro ⟨B, f⟩
        rfl }

lemma star_bijective (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Function.Bijective ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).star x) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact (starEquiv A x).bijective

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements
public import Mathlib.CategoryTheory.EqToHom

/-!
# 元の二方向要素圏の底の関手による変更

概要：底の関手と元の両ラベルをそのまま使う要素圏の比較を構成する。
方針：底の全射を関手で送り、元の二つのラベル等式を保持する。
規約：対象・射の新しい代表や逆像の選択を導入しない。
使われ方：DK9.5の元の比較射の底への自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite

variable {V W : Type u} [Category.{u} V] [Category.{u} W]
  (H : V ⥤ W) (F : Wᵒᵖ ⥤ Type u) (G : W ⥤ Type u)

def pre : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element (H.op ⋙ F) (H ⋙ G) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element F G where
  obj X := ⟨H.obj X.base, X.left, X.right⟩
  map f := ⟨H.map f.base, f.left, f.right⟩
  map_id X := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.hom_ext F G _ _ (H.map_id X.base)
  map_comp f g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.hom_ext F G _ _ (H.map_comp f.base g.base)

lemma pre_projection : pre H F G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.projection F G = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.projection _ _ ⋙ H := rfl

variable {F G} {F' : Wᵒᵖ ⥤ Type u} {G' : W ⥤ Type u}

lemma pre_naturality (α : F ⟶ F') (β : G ⟶ G') :
    pre H F G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map α β =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map (Functor.whiskerLeft H.op α) (Functor.whiskerLeft H β) ⋙ pre H F' G' := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.hom_ext F' G' _ _ rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

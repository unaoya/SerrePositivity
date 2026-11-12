module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck
public import Mathlib.CategoryTheory.EqToHom

/-!
# 元の二方向 Grothendieck の三成分による射の判定

概要：底の等式と左右の異種等式で元の全射を判定する。
方針：既存の元の Hom の三成分の全単射を使う。
規約：元の射を変更せず、端点移送の表示だけを吸収する。
使われ方：DK9.5の元の対角単体の関手則。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents
open CategoryTheory Opposite

private lemma sigma_pair_ext {I : Type u} {A B : I → Type u}
    (x y : Σ i, A i × B i) (hi : x.1 = y.1)
    (ha : HEq x.2.1 y.2.1) (hb : HEq x.2.2 y.2.2) : x = y := by
  rcases x with ⟨i, a, b⟩
  rcases y with ⟨j, a', b'⟩
  cases hi
  cases eq_of_heq ha
  cases eq_of_heq hb
  rfl

lemma unop_eqToHom_heq_id {D : Type u} [Category.{u} D] {A B : Dᵒᵖ} (h : A = B) :
    HEq (eqToHom h).unop (𝟙 B.unop) := by
  cases h
  rfl

lemma unop_eqToHom_comp_heq {D : Type u} [Category.{u} D]
    {A A' B E : Dᵒᵖ} (h : A' = A) (f : A ⟶ B) (g : B ⟶ E) :
    HEq ((eqToHom h ≫ f ≫ g).unop) (g.unop ≫ f.unop) := by
  cases h
  simp

variable {W : Type u} [Category.{u} W] {F : Wᵒᵖ ⥤ Cat.{u, u}} {G : W ⥤ Cat.{u, u}}

lemma hom_ext_heq {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G} (f g : X ⟶ Y) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap f = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap g)
    (hl : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap g)) (hr : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap g)) : f = g :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homEquiv X Y).injective (sigma_pair_ext _ _ hb hl hr)

lemma leftMap_id_heq (X : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G) : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap (𝟙 X)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.left F G X)) := by
  have h := congrArg Quiver.Hom.unop (Grothendieck.id_fiber X.base.unop)
  refine (heq_of_eq h).trans ?_
  exact unop_eqToHom_heq_id _

lemma rightMap_id_heq (X : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G) : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap (𝟙 X)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.right F G X)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap
  simp only [Grothendieck.id_fiber]
  exact eqToHom_heq_id_cod _ _ _

lemma leftMap_comp_heq {X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap (f ≫ g))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap f ≫ (F.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap f).op).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.leftMap g)) := by
  have h := congrArg Quiver.Hom.unop (Grothendieck.comp_fiber g.base.unop f.base.unop)
  refine (heq_of_eq h).trans ?_
  exact unop_eqToHom_comp_heq _ _ _

lemma rightMap_comp_heq {X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap (f ≫ g))
      ((G.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.baseMap g)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.rightMap g) := by
  change HEq (eqToHom _ ≫ _ ≫ _) _
  simp only [eqToHom_comp_heq_iff]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents

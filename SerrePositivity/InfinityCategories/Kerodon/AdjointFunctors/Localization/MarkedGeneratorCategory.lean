module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.Equivalence

/-!
# 元の指定矢の部分圏は指定生成矢の自由圏

概要：Paths C の指定矢 W.paths の部分圏と、W の生成矢だけの自由圏の圏同値。
方針：全文字の所属証明からの逆と、元の包含による射列の回収を使う。
規約：元の部分圏への包含との因子化も保持する。W の乗法性は不要。
使われ方：Dwyer–Kan 比較補題2.3の自由な W の実際の模型。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorCategory
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

def toWide : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) ⥤ WideSubcategory W.paths where
  obj X := ⟨X⟩
  map p := ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W).map p, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion_mem W p⟩
  map_id X := by apply WideSubcategory.hom_ext; rfl
  map_comp p q := by apply WideSubcategory.hom_ext; exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W).map_comp p q

def fromWide : WideSubcategory W.paths ⥤ Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) where
  obj X := X.obj
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.lift W f.hom f.property
  map_id X := rfl
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion_injective W
    dsimp only
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion_lift, Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion_lift, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion_lift]
    rfl

def equivalence : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) ≌ WideSubcategory W.paths where
  functor := toWide W
  inverse := fromWide W
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change f ≫ 𝟙 _ = 𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.lift W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W).map f) _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.lift_inclusion, Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents (fun X => eqToIso (by cases X; rfl)) (by
    intro X Y f
    cases X
    cases Y
    apply WideSubcategory.hom_ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.lift W f.hom _) ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion_lift, Category.comp_id, Category.id_comp])
  functor_unitIso_comp X := by
    apply WideSubcategory.hom_ext
    rfl

lemma toWide_inclusion : toWide W ⋙ wideSubcategoryInclusion W.paths = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorCategory

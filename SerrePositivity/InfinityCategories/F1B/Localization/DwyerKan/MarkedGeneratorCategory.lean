module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.MarkedGeneratorPaths
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.Equivalence

/-!
# 元の指定矢の部分圏は指定生成矢の自由圏

概要：Paths C の指定矢 W.paths の部分圏と、W の生成矢だけの自由圏の圏同値。
方針：全文字の所属証明からの逆と、元の包含による射列の回収を使う。
規約：元の部分圏への包含との因子化も保持する。W の乗法性は不要。
使われ方：Dwyer–Kan 比較補題2.3の自由な W の実際の模型。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization.MarkedGenerators
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

def toWide : Paths (quiver W) ⥤ WideSubcategory W.paths where
  obj X := ⟨X⟩
  map p := ⟨(inclusion W).map p, inclusion_mem W p⟩
  map_id X := by apply WideSubcategory.hom_ext; rfl
  map_comp p q := by apply WideSubcategory.hom_ext; exact (inclusion W).map_comp p q

def fromWide : WideSubcategory W.paths ⥤ Paths (quiver W) where
  obj X := X.obj
  map f := lift W f.hom f.property
  map_id X := rfl
  map_comp f g := by
    apply inclusion_injective W
    dsimp only
    rw [inclusion_lift, Functor.map_comp, inclusion_lift, inclusion_lift]
    rfl

def equivalence : Paths (quiver W) ≌ WideSubcategory W.paths where
  functor := toWide W
  inverse := fromWide W
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change f ≫ 𝟙 _ = 𝟙 _ ≫ lift W ((inclusion W).map f) _
    rw [lift_inclusion, Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents (fun X => eqToIso (by cases X; rfl)) (by
    intro X Y f
    cases X
    cases Y
    apply WideSubcategory.hom_ext
    change (inclusion W).map (lift W f.hom _) ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    rw [inclusion_lift, Category.comp_id, Category.id_comp])
  functor_unitIso_comp X := by
    apply WideSubcategory.hom_ext
    rfl

lemma toWide_inclusion : toWide W ⋙ wideSubcategoryInclusion W.paths = inclusion W := rfl

end SerrePositivity.EInfinity.SimplicialLocalization.MarkedGenerators

module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedGeneratorWord

/-!
# 非指定生成文字列への元の自由圏の関手

概要：元の自由圏を非指定生成文字列の一対象圏へ移し、指定射列を恒等射へ送る。
方針：列の連結を合成とし、元の erase の連結則を使う。
規約：文字には元の始域・終域・射を残す。モデル構造は使わない。
使われ方：既存の zigzag 評価による全語・全縦射で不変な非指定文字列。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization.GeneratorWord
open CategoryTheory

variable {C : Type u} [Category.{v} C]

def WordObject (_C : Type u) : Type (max u v) := PUnit

instance wordCategory : Category.{max u v} (WordObject.{u, v} C) where
  Hom _ _ := List (Quiver.Total C)
  id _ := []
  comp p q := p ++ q
  id_comp _ := List.nil_append _
  comp_id _ := List.append_nil _
  assoc _ _ _ := List.append_assoc _ _ _

def functor (W : MorphismProperty C) : Paths C ⥤ WordObject.{u, v} C where
  obj _ := PUnit.unit
  map p := erase W p
  map_id _ := rfl
  map_comp p q := erase_comp W p q

lemma inverts (W : MorphismProperty C) : W.paths.IsInvertedBy (functor W) := by
  intro X Y p hp
  have he : (functor W).map p = 𝟙 ((functor W).obj X) := erase_marked W p hp
  rw [he]
  infer_instance

end SerrePositivity.EInfinity.SimplicialLocalization.GeneratorWord

module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValueAppendPaths

/-!
# 元の反転関手による zigzag の連結の評価

概要：元の二つの zigzag の連結の値は、同じ元の二つの値の合成となる。
方針：値の射列を元の接合点で分割し、左右への制限の回収式を使う。
規約：左右の空語と元の全端点移送を保持する。
使われ方：元の全 hammock 評価の豊穣合成との整合。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Value
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} (L : C ⥤ D) (hL : W.IsInvertedBy L)
  {a b : Word} {X Y Z : C}

lemma value_append (S : Zigzag W a X Y) (T : Zigzag W b Y Z) :
    value L hL (ZigzagAppend.obj S T) = value L hL S ≫ value L hL T := by
  have hp : (path L hL (ZigzagAppend.obj S T)).hom =
      (path L hL (ZigzagAppend.obj S T)).map
        (homOfLE (Fin.zero_le (Word.leftVertex a b (Fin.last a.length)))) ≫
      (path L hL (ZigzagAppend.obj S T)).map
        (homOfLE (Fin.le_last (Word.rightVertex a b 0))) :=
    (path L hL (ZigzagAppend.obj S T)).map_comp _ _
  unfold value
  rw [hp, path_append_left_hom, path_append_right_hom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

end SerrePositivity.EInfinity.Hammock.Zigzag.Value

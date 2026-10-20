module

public import SerrePositivity.EInfinity.Hammock.ZigzagAppendObjects
public import SerrePositivity.EInfinity.Hammock.DirectionArrowComparison

/-!
# 連結の左右の列の向き付き比較

概要：連結の左右の元の列を、同じ向きに応じた圏でも比較する。
方針：元の全列の異種等式と、元の両端の等式を使う。
規約：接合点の移送は元の端点の等式だけによる。
使われ方：連結の左右の同方向の区間合成の回収。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word} {X Y Z : C}

lemma direction_left_heq (S : Zigzag W a X Y) (T : Zigzag W b Y Z) (d : Direction)
    (i : Fin a.length) (hi : a.direction i = d) :
    HEq (Direction.arrow d (obj S T) (i.castAdd b.length)
      ((Word.append_direction_left a b i).trans hi)) (Direction.arrow d S i hi) :=
  Direction.arrow_heq_of (obj S T) S d _ _ _ _
    (source_left_eq S T i) (target_left_eq S T i) (arrow_left_heq S T i)

lemma direction_right_heq (S : Zigzag W a X Y) (T : Zigzag W b Y Z) (d : Direction)
    (i : Fin b.length) (hi : b.direction i = d) :
    HEq (Direction.arrow d (obj S T) (i.natAdd a.length)
      ((Word.append_direction_right a b i).trans hi)) (Direction.arrow d T i hi) :=
  Direction.arrow_heq_of (obj S T) T d _ _ _ _
    (source_right_eq S T i) (target_right_eq S T i) (arrow_right_heq S T i)

end SerrePositivity.EInfinity.Hammock.ZigzagAppend

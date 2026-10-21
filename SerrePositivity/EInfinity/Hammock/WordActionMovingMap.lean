module

public import SerrePositivity.EInfinity.Hammock.WordAction
public import SerrePositivity.EInfinity.Hammock.MovingSegmentNaturality

/-!
# 元の WordAction と動く端点の全縦射

概要：元の語の作用を、端点も動く全縦射へ適用する。
方針：元の列の区間合成の正方形と同じ cut を使う。
規約：固定端点では既存の WordAction.map と同じ成分を持つ。
使われ方：内部の三列 collapse を前後の全語へ貼る。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.WordAction
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : Word} {X Y X' Y' : C} {S : Zigzag W a X Y} {T : Zigzag W a X' Y'}

omit [W.IsMultiplicative] in
lemma moving_segment_square (d : Direction) (g : Zigzag.MovingHom S T)
    (p q : Fin (a.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d) :
    square d (Segment.map d S p q hpq hd) (Segment.map d T p q hpq hd) (g.app p) (g.app q) := by
  cases d
  · exact Segment.Moving.forward_map_comm g p q hpq hd
  · exact Segment.Moving.backward_map_comm g p q hpq hd

omit [W.IsMultiplicative] in
lemma moving_column_comm (f : a ⟶ b) (g : Zigzag.MovingHom S T) (j : Fin b.length) :
    column f S j ≫ g.app (f.cut (b.target j)) =
      g.app (f.cut (b.source j)) ≫ column f T j :=
  columnAux_comm (fun k => S.vertex (f.cut k)) (fun k => T.vertex (f.cut k))
    (fun k => g.app (f.cut k)) _ _ _ _ _ (moving_segment_square _ g _ _ _ _)

def movingMap (f : a ⟶ b) (g : Zigzag.MovingHom S T) :
    Zigzag.MovingHom (obj f S) (obj f T) where
  app j := g.app (f.cut j)
  app_mem j := g.app_mem (f.cut j)
  comm j := moving_column_comm f g j

lemma movingMap_id (f : a ⟶ b) (S : Zigzag W a X Y) :
    movingMap f (Zigzag.MovingHom.id S) = Zigzag.MovingHom.id (obj f S) := by
  apply Zigzag.MovingHom.ext
  intro j
  rfl

lemma movingMap_comp (f : a ⟶ b) {X'' Y'' : C} {U : Zigzag W a X'' Y''}
    (g : Zigzag.MovingHom S T) (h : Zigzag.MovingHom T U) :
    movingMap f (g.comp h) = (movingMap f g).comp (movingMap f h) := by
  apply Zigzag.MovingHom.ext
  intro j
  rfl

end SerrePositivity.EInfinity.Hammock.WordAction

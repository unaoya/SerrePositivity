module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingSegmentNaturality

/-!
# 元の WordAction と動く端点の全縦射

概要：元の語の作用を、端点も動く全縦射へ適用する。
方針：元の列の区間合成の正方形と同じ cut を使う。
規約：固定端点では既存の WordAction.map と同じ成分を持つ。
使われ方：内部の三列 collapse を前後の全語へ貼る。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y X' Y' : C} {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X' Y'}

omit [W.IsMultiplicative] in
lemma moving_segment_square (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T)
    (p q : Fin (a.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.square d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S p q hpq hd) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d T p q hpq hd) (g.app p) (g.app q) := by
  cases d
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingSegmentNaturality.forward_map_comm g p q hpq hd
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingSegmentNaturality.backward_map_comm g p q hpq hd

omit [W.IsMultiplicative] in
lemma moving_column_comm (f : a ⟶ b) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) (j : Fin b.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column f S j ≫ g.app (f.cut (b.target j)) =
      g.app (f.cut (b.source j)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column f T j :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.columnAux_comm (fun k => S.vertex (f.cut k)) (fun k => T.vertex (f.cut k))
    (fun k => g.app (f.cut k)) _ _ _ _ _ (moving_segment_square _ g _ _ _ _)

def movingMap (f : a ⟶ b) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f T) where
  app j := g.app (f.cut j)
  app_mem j := g.app_mem (f.cut j)
  comm j := moving_column_comm f g j

lemma movingMap_id (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) :
    movingMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id S) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
  intro j
  rfl

lemma movingMap_comp (f : a ⟶ b) {X'' Y'' : C} {U : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X'' Y''}
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom T U) :
    movingMap f (g.comp h) = (movingMap f g).comp (movingMap f h) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
  intro j
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

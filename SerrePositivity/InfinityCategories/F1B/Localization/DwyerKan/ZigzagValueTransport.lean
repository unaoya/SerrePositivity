module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValuePath
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagEndpointChange

/-!
# 元の関手・端点の等式による zigzag の値の移送

概要：関手または端点の表示を等式で戻した値は、元の値と異種等しい。
方針：元の等式を消去し、元の同じ全射列へ戻す。
規約：新しい同型や逆射の選択を加えない。
使われ方：固定対象の自由解像の通常の局所化 Hom との比較。
-/

@[expose] public section
universe u v u' v'
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Value
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} {w : Word} {X Y X' Y' : C}

lemma value_functor_congr {L M : C ⥤ D} (h : L = M)
    (hL : W.IsInvertedBy L) (hM : W.IsInvertedBy M) (S : Zigzag W w X Y) :
    HEq (value L hL S) (value M hM S) := by
  cases h
  rfl

lemma value_endpoint_change (L : C ⥤ D) (hL : W.IsInvertedBy L)
    (hX : X = X') (hY : Y = Y') (S : Zigzag W w X Y) :
    HEq (value L hL (EndpointChange.obj hX hY S)) (value L hL S) := by
  cases hX
  cases hY
  rfl

end SerrePositivity.EInfinity.Hammock.Zigzag.Value

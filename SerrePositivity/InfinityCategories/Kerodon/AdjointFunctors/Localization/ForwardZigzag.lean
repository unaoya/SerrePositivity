module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHom
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# 元の forward 一列と動く端点の正方形

概要：元の一つの射とその可換正方形を、同じ頂点・列・縦射の zigzag へ移す。
方針：二つの頂点と一つの射をそのまま使う。
規約：両端の縦射は元の指定射であり、恒等射に固定しない。
使われ方：列内部の切断を前後の全語へ接続する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {X Y X' Y' : C}

def obj (e : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) X Y where
  vertex := Fin.cons X (fun _ => Y)
  first := rfl
  last := rfl
  arrow i := by
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact e
  backward_mem _ hi := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction.noConfusion hi

def movingHom {e : X ⟶ Y} {e' : X' ⟶ Y'}
    (x : X ⟶ X') (y : Y ⟶ Y') (hx : W x) (hy : W y) (h : e ≫ y = x ≫ e') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (obj (W := W) e) (obj e') where
  app i := by
    change Fin 2 at i
    cases i using Fin.cases with
    | zero => exact x
    | succ _ => exact y
  app_mem i := by
    cases i using Fin.cases with
    | zero => exact hx
    | succ _ => exact hy
  comm i := by
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag

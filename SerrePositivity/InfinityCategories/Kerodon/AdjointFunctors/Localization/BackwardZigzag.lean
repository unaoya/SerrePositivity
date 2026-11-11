module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHom
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# 元の backward 一列と動く端点の正方形

概要：指定された弱同値を元の一列の zigzag にし、その可換正方形も保持する。
方針：二つの頂点と一つの射をそのまま使う。
規約：両端の縦射は恒等射を要求せず、元の弱同値であることを記録する。
使われ方：forward ブロックの置換を両端の backward 列へ合成する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {X Y X' Y' : C}

def obj (e : Y ⟶ X) (he : W e) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y where
  vertex := Fin.cons X (fun _ => Y)
  first := rfl
  last := rfl
  arrow i := by
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact e
  backward_mem i _ := by
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact he

def movingHom {e : Y ⟶ X} {e' : Y' ⟶ X'} (he : W e) (he' : W e')
    (x : X ⟶ X') (y : Y ⟶ Y') (hx : W x) (hy : W y) (h : e ≫ x = y ≫ e') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (obj e he) (obj e' he') where
  app i := by
    change Fin 2 at i
    cases i using Fin.cases with
    | zero => exact x
    | succ i => exact y
  app_mem i := by
    cases i using Fin.cases with
    | zero => exact hx
    | succ i => exact hy
  comm i := by
    change Fin 1 at i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag

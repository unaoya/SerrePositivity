module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentNaturality
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# 元の指定矢を反転する関手による zigzag の値

概要：元の各列を順方向の射にし、元の両端を持つ一つの射へ合成する。
方針：forward 列には関手、backward 列にはその像の逆射を使う。
規約：任意の反転関手に対して構成し、空語と元の端点の等式を保持する。
使われ方：元の hammock から通常の局所化 Hom への評価。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} (L : C ⥤ D) (hL : W.IsInvertedBy L)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

def backwardIso (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length) (hi : w.direction i = .backward) :
    L.obj (S.vertex i.succ) ≅ L.obj (S.vertex i.castSucc) := by
  have : IsIso (L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward S i hi).unop) :=
    hL _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow_allowed .backward S i hi)
  exact asIso (L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward S i hi).unop)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.backwardIso export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath (backwardIso)


def edge (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length) :
    L.obj (S.vertex i.castSucc) ⟶ L.obj (S.vertex i.succ) :=
  match hi : w.direction i with
  | .forward => L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S i hi)
  | .backward => (backwardIso L hL S i hi).inv

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.edge export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath (edge)


lemma edge_forward (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length) (hi : w.direction i = .forward) :
    edge L hL S i = L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S i hi) := by
  dsimp only [edge]
  split
  · rfl
  · rename_i hb
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction.backward = .forward := hb.symm.trans hi
    cases h

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.edge_forward export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath (edge_forward)


lemma edge_backward (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length) (hi : w.direction i = .backward) :
    edge L hL S i = (backwardIso L hL S i hi).inv := by
  dsimp only [edge]
  split
  · rename_i hf
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction.forward = .backward := hf.symm.trans hi
    cases h
  · rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.edge_backward export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath (edge_backward)


def path (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) : ComposableArrows D w.length :=
  ComposableArrows.mkOfObjOfMapSucc (fun j => L.obj (S.vertex j)) (edge L hL S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.path export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath (path)


def value (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) : L.obj X ⟶ L.obj Y :=
  eqToHom (congrArg L.obj S.first.symm) ≫ (path L hL S).hom ≫
    eqToHom (congrArg L.obj S.last)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.value export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath (value)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath

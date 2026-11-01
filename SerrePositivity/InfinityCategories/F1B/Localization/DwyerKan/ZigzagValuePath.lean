module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SegmentNaturality
public import Mathlib.CategoryTheory.Localization.Construction

/-!
# 元の指定矢を反転する関手による zigzag の値

概要：元の各列を順方向の射にし、元の両端を持つ一つの射へ合成する。
方針：forward 列には関手、backward 列にはその像の逆射を使う。
規約：任意の反転関手に対して構成し、空語と元の端点の等式を保持する。
使われ方：元の hammock から通常の局所化 Hom への評価。
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
  {w : Word} {X Y : C}

def backwardIso (S : Zigzag W w X Y) (i : Fin w.length) (hi : w.direction i = .backward) :
    L.obj (S.vertex i.succ) ≅ L.obj (S.vertex i.castSucc) := by
  have : IsIso (L.map (Direction.arrow .backward S i hi).unop) :=
    hL _ (Direction.arrow_allowed .backward S i hi)
  exact asIso (L.map (Direction.arrow .backward S i hi).unop)

def edge (S : Zigzag W w X Y) (i : Fin w.length) :
    L.obj (S.vertex i.castSucc) ⟶ L.obj (S.vertex i.succ) :=
  match hi : w.direction i with
  | .forward => L.map (Direction.arrow .forward S i hi)
  | .backward => (backwardIso L hL S i hi).inv

lemma edge_forward (S : Zigzag W w X Y) (i : Fin w.length) (hi : w.direction i = .forward) :
    edge L hL S i = L.map (Direction.arrow .forward S i hi) := by
  dsimp only [edge]
  split
  · rfl
  · rename_i hb
    have h : Direction.backward = .forward := hb.symm.trans hi
    cases h

lemma edge_backward (S : Zigzag W w X Y) (i : Fin w.length) (hi : w.direction i = .backward) :
    edge L hL S i = (backwardIso L hL S i hi).inv := by
  dsimp only [edge]
  split
  · rename_i hf
    have h : Direction.forward = .backward := hf.symm.trans hi
    cases h
  · rfl

def path (S : Zigzag W w X Y) : ComposableArrows D w.length :=
  ComposableArrows.mkOfObjOfMapSucc (fun j => L.obj (S.vertex j)) (edge L hL S)

def value (S : Zigzag W w X Y) : L.obj X ⟶ L.obj Y :=
  eqToHom (congrArg L.obj S.first.symm) ≫ (path L hL S).hom ≫
    eqToHom (congrArg L.obj S.last)

end SerrePositivity.EInfinity.Hammock.Zigzag.Value

module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Basic
public import Mathlib.AlgebraicGeometry.Limits

/-!
概要：同じ増大 nerve の基底への射と、全タプルの添字を定める。
方針：増大点では恒等射と空タプル、正次数では元の wide pullback を使う。
規約：増大点と通常の次数の座標を同じ増大単体圏で保持する。
使われ方：二つの幾何的 nerve の同じアフィン被覆（計画 P01〜P05）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.isDefEq.respectTransparency false

/-- 実際の増大 Čech nerve の各対象の元の基底への射。 -/
def augmentedNerveBase {X S : Scheme.{u}} (f : X ⟶ S)
    (a : AugmentedSimplexCategory) :
    (AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
      (Arrow.mk f).augmentedCechNerve).obj (op a) ⟶ S :=
  (AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse.obj
    (Arrow.mk f).augmentedCechNerve).map (WithInitial.starInitial.to a).op

/-- 増大点は空タプル、通常の n 次では長さ n+1 のタプル。 -/
def augmentedTupleLength (a : AugmentedSimplexCategory) : ℕ :=
  match a with
  | .star => 0
  | .of n => n.len + 1

/-- 増大単体圏の射の、同じタプルの位置への写像。 -/
def augmentedTupleIndexMap {a b : AugmentedSimplexCategory} (α : a ⟶ b) :
    Fin (augmentedTupleLength a) → Fin (augmentedTupleLength b) :=
  match a, b, α with
  | .star, _, _ => Fin.elim0
  | .of _, .of _, α => (WithInitial.down α).toOrderHom
  | .of _, .star, α => PEmpty.elim α

/-- 元の増大単体圏の恒等射は位置の恒等写像。 -/
theorem augmentedTupleIndexMap_id (a : AugmentedSimplexCategory) :
    augmentedTupleIndexMap (𝟙 a) = id := by
  cases a with
  | star => funext i; exact Fin.elim0 i
  | of n => rfl

/-- 元の増大単体圏の合成は、同じ位置写像の合成。 -/
theorem augmentedTupleIndexMap_comp {a b c : AugmentedSimplexCategory}
    (α : a ⟶ b) (β : b ⟶ c) :
    augmentedTupleIndexMap (α ≫ β) = augmentedTupleIndexMap β ∘ augmentedTupleIndexMap α := by
  cases a with
  | star => funext i; exact Fin.elim0 i
  | of a =>
    cases b with
    | star => exact PEmpty.elim α
    | of b =>
      cases c with
      | star => exact PEmpty.elim β
      | of c => rfl

end SerrePositivity.AlgebraicGeometry

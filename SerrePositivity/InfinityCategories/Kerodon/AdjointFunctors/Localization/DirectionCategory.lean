module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag
public import Mathlib.CategoryTheory.Opposites

/-!
# 向きに応じた元の圏と反対圏

概要：同方向の列を一つの合成可能射列として扱うための向きの界面。
方針：前向きでは元の圏、後ろ向きでは反対圏を使う。
規約：前向きの射は任意、後ろ向きの射には元の指定弱同値を要求する。
使われ方：空区間を含む同方向列の合成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory
open CategoryTheory Opposite

/-- 向きに応じた圏の対象の型。 -/
def category (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (C : Type u) : Type u :=
  match d with
  | .forward => C
  | .backward => Cᵒᵖ

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory (category)


instance (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (C : Type u) [Category.{v} C] : Category.{v} (category d C) :=
  match d with
  | .forward => inferInstanceAs (Category C)
  | .backward => inferInstanceAs (Category Cᵒᵖ)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory (instCategoryCategory)


/-- 元の頂点を向きに応じた圏へ移す。 -/
def vertex (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) {C : Type u} (X : C) : category d C :=
  match d with
  | .forward => X
  | .backward => op X

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory (vertex)


/-- 前向きの列は任意、後ろ向きの列は指定弱同値。 -/
def allowed (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) {C : Type u} [Category.{v} C] (W : MorphismProperty C) :
    MorphismProperty (category d C) :=
  match d with
  | .forward => ⊤
  | .backward => W.op

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory (allowed)


instance (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) {C : Type u} [Category.{v} C] (W : MorphismProperty C)
    [W.IsMultiplicative] : (allowed d W).IsMultiplicative := by
  cases d
  · exact inferInstanceAs (⊤ : MorphismProperty C).IsMultiplicative
  · exact inferInstanceAs W.op.IsMultiplicative

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory (instIsMultiplicativeCategoryAllowed)


variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

/-- 同じ向きの列を、向きに応じた圏の前向きの射として扱う。 -/
def arrow (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length)
    (hi : w.direction i = d) : vertex d (S.vertex i.castSucc) ⟶ vertex d (S.vertex i.succ) := by
  cases d
  · exact (eqToHom (congrArg S.vertex (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, hi]))) ≫ S.arrow i ≫
      eqToHom (congrArg S.vertex (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, hi]))
  · exact ((eqToHom (congrArg S.vertex (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, hi]))) ≫ S.arrow i ≫
      eqToHom (congrArg S.vertex (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, hi]))).op

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory (arrow)


/-- 等式だけによる両端点の移送は、元の射の類を変更しない。 -/
lemma transport_mem {A A' B B' : C} (hA : A' = A) (hB : B = B') (f : A ⟶ B) :
    W (eqToHom hA ≫ f ≫ eqToHom hB) ↔ W f := by
  cases hA
  cases hB
  simp

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory (transport_mem)


/-- 後ろ向きの列に課された元の弱同値は、向きを移しても保持される。 -/
lemma arrow_allowed (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length)
    (hi : w.direction i = d) : allowed d W (arrow d S i hi) := by
  cases d
  · trivial
  · change W (eqToHom _ ≫ S.arrow i ≫ eqToHom _)
    exact (transport_mem _ _ _).2 (S.backward_mem i hi)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory (arrow_allowed)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory

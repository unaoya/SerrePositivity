module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.SpecialHammock
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# 特殊な三本矢の元の普通の局所化への値

概要：Dwyer–Kan §7 の共通対象の各三本矢を元の局所化射へ送る。
方針：両脚を同じ局所化で反転し、全可換縦射で値が保存されることを証明する。
規約：比較値は元の左脚・中間射・右脚から作る。
使われ方：高次比較の共通図式と元の π₀ 正規化の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

/-- 概要：特殊な三本矢を元の局所化の同じ射へ送る（Dwyer–Kan §7）。
方針：元の両脚の弱同値を反転して中間射を挟む。
規約：元の局所化関手 Q を使う。
使われ方：共通比較の零次の正規化。 -/
def value (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y) :
    (weakEquivalences C).Q.obj X ⟶ (weakEquivalences C).Q.obj Y := by
  let Q := (weakEquivalences C).Q
  have : IsIso (Q.map S.leftMap) :=
    Localization.inverts Q (weakEquivalences C) _ S.left_mem.2
  have : IsIso (Q.map S.rightMap) :=
    Localization.inverts Q (weakEquivalences C) _ S.right_mem.2
  exact inv (Q.map S.leftMap) ≫ Q.map S.middle ≫ inv (Q.map S.rightMap)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison (value)


/-- 概要：特殊な三本矢の全可換縦射は元の局所化の値を保つ（Dwyer–Kan §7）。
方針：両端の可逆射で挟み、元の三つの可換式を局所化へ送る。
規約：縦射や逆射の追加の選択を要求しない。
使われ方：共通比較先の nerve の全単体の値。 -/
lemma value_eq {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y} (f : S ⟶ T) : value S = value T := by
  let Q := (weakEquivalences C).Q
  have : IsIso (Q.map S.leftMap) :=
    Localization.inverts Q (weakEquivalences C) _ S.left_mem.2
  have : IsIso (Q.map S.rightMap) :=
    Localization.inverts Q (weakEquivalences C) _ S.right_mem.2
  have : IsIso (Q.map T.leftMap) :=
    Localization.inverts Q (weakEquivalences C) _ T.left_mem.2
  have : IsIso (Q.map T.rightMap) :=
    Localization.inverts Q (weakEquivalences C) _ T.right_mem.2
  have hl : Q.map f.left ≫ Q.map T.leftMap = Q.map S.leftMap := by
    rw [← Q.map_comp, f.left_w]
  have hr : Q.map S.rightMap ≫ Q.map f.right = Q.map T.rightMap := by
    rw [← Q.map_comp, f.right_w]
  have hm : Q.map S.middle ≫ Q.map f.right = Q.map f.left ≫ Q.map T.middle := by
    rw [← Q.map_comp, ← Q.map_comp, f.middle_w]
  apply (cancel_epi (Q.map S.leftMap)).1
  apply (cancel_mono (Q.map T.rightMap)).1
  calc
    (Q.map S.leftMap ≫ value S) ≫ Q.map T.rightMap = Q.map S.middle ≫ Q.map f.right := by
      rw [← hr]
      simp [value, Q, Category.assoc]
    _ = Q.map f.left ≫ Q.map T.middle := hm
    _ = (Q.map S.leftMap ≫ value T) ≫ Q.map T.rightMap := by
      rw [← hl]
      simp [value, Q, Category.assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison (value_eq)


/-- 概要：特殊な三本矢の値は普通の局所化 Hom の離散圏への関手（Dwyer–Kan §7）。
方針：全縦射で保存される同じ値を等式の射へ送る。
規約：特殊な三本矢の圏や Hom 自体を離散化しない。
使われ方：高次の共通比較の元の局所化射の照合。 -/
def valueFunctor (X Y : C) : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y ⥤
    Discrete ((weakEquivalences C).Q.obj X ⟶ (weakEquivalences C).Q.obj Y) where
  obj S := Discrete.mk (value S)
  map f := eqToHom (congrArg Discrete.mk (value_eq f))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison (valueFunctor)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.ArrowSpan
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# モデル圏の特殊な三本矢と縦射の弱同値性

概要：Dwyer–Kan §7 の共通比較の圏を実際の trivial な両脚へ特殊化する。
方針：左脚を trivial fibration、右脚を trivial cofibration とし、二つの縦射の弱同値性を導く。
規約：モデル構造は元の圏にだけ要求し、単体集合のモデル構造は要求しない。
使われ方：既存の frame Hom と hammock の全単体の共通図式。
-/

@[expose] public section

universe u v

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- 概要：モデル圏の特殊な三本矢の圏（Dwyer–Kan §7）。
方針：元の三本矢の両脚を実際の trivial な射の類へ代入する。
規約：中間射や元の両対象に cofibrancy・fibrancy を要求しない。
使われ方：frame と単体的局所化の比較の共通対象。 -/
abbrev SpecialHammock (X Y : C) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object (trivialFibrations C) (trivialCofibrations C) X Y

namespace SpecialHammock

variable {X Y : C} {S T : SpecialHammock X Y}

/-- 概要：特殊な三本矢の左の縦射は弱同値（Dwyer–Kan §7）。
方針：同じ trivial な左脚二本と可換性から二つのうち三つを使う。
規約：縦射の弱同値性を追加入力にしない。
使われ方：実際の特殊な hammock の全縦射の条件。 -/
lemma left_weakEquivalence (f : S ⟶ T) : weakEquivalences C f.left := by
  apply (weakEquivalences C).of_postcomp _ T.leftMap T.left_mem.2
  exact f.left_w.symm ▸ S.left_mem.2

/-- 概要：特殊な三本矢の右の縦射も弱同値（Dwyer–Kan §7）。
方針：同じ trivial な右脚二本と可換性から二つのうち三つを使う。
規約：右脚の方向は Y から中間対象へ向かう。
使われ方：実際の特殊な hammock の全縦射の条件。 -/
lemma right_weakEquivalence (f : S ⟶ T) : weakEquivalences C f.right := by
  apply (weakEquivalences C).of_precomp S.rightMap _ S.right_mem.2
  exact f.right_w.symm ▸ T.right_mem.2

end SpecialHammock

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.SpecialHammock
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.ArrowSpanInclusion
public import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# 両脚が弱同値の元の三本矢

概要：特殊な三本矢と比較する、弱同値の両脚を持つ三本矢の圏を定める。
方針：元の ArrowSpan に弱同値の類を代入し、片脚を自明にした包含を作る。
規約：縦射の弱同値性は追加入力ではなく両脚の可換性から導く。
使われ方：Low 命題3.5 の特殊な三本矢から一般の三本矢への比較。
-/

@[expose] public section
universe u v
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- 両脚が元の弱同値である三本矢の圏。 -/
abbrev WeakThreeArrow (X Y : C) := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object (weakEquivalences C) (weakEquivalences C) X Y

/-- 左脚を元の自明 fibration に限定した中間の三本矢の圏。 -/
abbrev LeftTrivialThreeArrow (X Y : C) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object (trivialFibrations C) (weakEquivalences C) X Y

namespace WeakThreeArrow
variable {X Y : C}

/-- 特殊な右脚の条件を広げる同じ三本矢の包含。 -/
abbrev specialInclusion : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y ⥤ LeftTrivialThreeArrow X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.inclusion (fun _ _ _ h => h) (fun _ _ _ h => h.2)

/-- 自明な左脚の条件を広げる同じ三本矢の包含。 -/
abbrev leftInclusion : LeftTrivialThreeArrow X Y ⥤ WeakThreeArrow X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.inclusion (fun _ _ _ h => h.2) (fun _ _ _ h => h)

/-- 元の弱同値の両左脚から、元の左の縦射の弱同値性を得る。 -/
lemma left_weakEquivalence {S T : WeakThreeArrow X Y} (f : S ⟶ T) :
    weakEquivalences C f.left := by
  apply (weakEquivalences C).of_postcomp _ T.leftMap T.left_mem
  exact f.left_w.symm ▸ S.left_mem

/-- 元の弱同値の両右脚から、元の右の縦射の弱同値性を得る。 -/
lemma right_weakEquivalence {S T : WeakThreeArrow X Y} (f : S ⟶ T) :
    weakEquivalences C f.right := by
  apply (weakEquivalences C).of_precomp S.rightMap _ S.right_mem
  exact f.right_w.symm ▸ T.right_mem

end WeakThreeArrow
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

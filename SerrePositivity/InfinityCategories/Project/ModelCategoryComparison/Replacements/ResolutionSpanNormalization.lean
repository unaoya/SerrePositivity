module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ResolutionSpecialSpans
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Localizations.SpecialSpanLocalization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PiZero

/-!
# 全単体の特殊な三本矢の図式と元の π₀ の同定の整合

概要：Dwyer–Kan §7 の共通図式が既存の frame Hom の元の零次比較を保持する。
方針：同じ augmentation・fibrant 置換の局所化射を元の π₀ の式と照合する。
規約：別の局所化射や Map^h の比較を選ばない。
使われ方：後続の高次比較の同じ元の射での正規化。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory HomotopicalAlgebra Opposite
open _root_.SerrePositivity.Reedy _root_.SerrePositivity.HomotopyFunctionComplex
open scoped _root_.Simplicial

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- 概要：元の零単体の三本矢の値は既存の π₀ 同値の同じ局所化射（Dwyer–Kan §7）。
方針：両脚の同じ逆射と既存の chosenResolutionHomPiZeroEquiv の元の式を使う。
規約：元の関手的分解・augmentation・右の置換を保持する。
使われ方：高次比較の frame 側の零次の正規化。 -/
lemma chosenResolutionSpanValue_zero
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X Y : C) (f : (((chosenResolutionHom cof fib).obj (op X)).obj Y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.value ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.chosenResolutionSpanFunctor cof fib X Y).obj
        (op ((((chosenResolutionHom cof fib).obj (op X)).obj Y).elementsMk (op ⦋0⦌) f))) =
      chosenResolutionHomPiZeroEquiv (weakEquivalences C).Q cof fib (op X) Y (SSet.π₀.mk f) := by
  rw [chosenResolutionHomPiZeroEquiv_mk]
  rfl

/-- 概要：共通図式の全単体作用素で元の局所化の値は保存される（Dwyer–Kan §7）。
方針：実際の三本矢の関手の全作用素へ値の可換性を適用する。
規約：全ての単体と全ての面・退化を含む。
使われ方：元の零次正規化を全比較図式に沿って保持する。 -/
lemma chosenResolutionSpanValue_naturality
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X Y : C) {s t : ((((chosenResolutionHom cof fib).obj (op X)).obj Y).Elements)ᵒᵖ}
    (f : s ⟶ t) :
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.value ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.chosenResolutionSpanFunctor cof fib X Y).obj s) =
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.value ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.chosenResolutionSpanFunctor cof fib X Y).obj t) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.value_eq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.chosenResolutionSpanFunctor cof fib X Y).map f)

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

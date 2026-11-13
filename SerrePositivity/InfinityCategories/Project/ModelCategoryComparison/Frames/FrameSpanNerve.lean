module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ResolutionSpecialSpans
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Category.ULift

/-!
# 全単体の frame 図式から特殊な三本矢の nerve への射

概要：Dwyer–Kan §7 の共通比較の frame 側の図式を実際の単体集合の射へ送る。
方針：要素圏の Hom の宇宙だけを揃え、同じ全単体の関手へ普通の nerve を適用する。
規約：元の単体と全作用素を保持する。比較の弱同値性は後続。
使われ方：元の Map^h と特殊な hammock の nerve の共通比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

open CategoryTheory HomotopicalAlgebra Opposite
open _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C]

/-- 概要：元の全単体の三本矢の図式は実際の nerve の射を与える（Dwyer–Kan §7）。
方針：元の全単体の関手の Hom の宇宙だけを調整して nerve で送る。
規約：固定 Hom の全単体・作用素・元の三本矢を保持する。
使われ方：特殊な hammock の共通比較の frame 側の射。 -/
def frameElementSpanNerveMap (L R : MorphismProperty C) {X Y Z : C}
    (A : SimplexCategory ⥤ C) (p : A ⟶ (Functor.const SimplexCategory).obj X)
    (hp : ∀ n, L (p.app n)) (j : Y ⟶ Z) (hj : R j) :
    nerve (ULiftHom.{max u v} ((((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z).Elements)ᵒᵖ)) ⟶
      nerve (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Object L R X Y) where
  app _ := ↾fun c => c ⋙ (ULiftHom.down.{0, v, max u v}
    (C := (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Z).Elements)ᵒᵖ)) ⋙
      _root_.SerrePositivity.EInfinity.FrameHom.frameElementSpanFunctor L R A p hp j hj
  naturality _ _ _ := rfl

variable [ModelCategory C]

/-- 概要：元の chosenResolutionHom の全単体図式の特殊な hammock の nerve への射（Dwyer–Kan）。
方針：同じ二つの分解を全単体の nerve 比較へ代入する。
規約：元の Hom と分解を選び直さず、単体集合モデルも入力しない。
使われ方：実際の E 代数の高次の共通比較。 -/
def chosenResolutionSpanNerveMap
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (X Y : C) :
    nerve (ULiftHom.{max u v}
      (((((chosenResolutionHom cof fib).obj (op X)).obj Y).Elements)ᵒᵖ)) ⟶
        nerve (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y) where
  app _ := ↾fun c => c ⋙ (ULiftHom.down.{0, v, max u v}
    (C := ((((chosenResolutionHom cof fib).obj (op X)).obj Y).Elements)ᵒᵖ)) ⋙
      _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.chosenResolutionSpanFunctor cof fib X Y
  naturality _ _ _ := rfl

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

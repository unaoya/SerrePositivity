module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFactorization
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ForwardPathBoundaryComparisonEndpoints

/-!
# 元の二つの forward ブロックと三つの脚の図式

概要：同じ添字圏で動く元の左右射列・三つの自然な脚から、全体を貼る。
方針：脚を評価関手への自然変換として記録し、元の全縦弱同値を保持する。
規約：添字圏の端点は全体の X,Y のみ固定する。弱同値の結論を入力しない。
使われ方：中央 backward 列の置換関手と比較自然変換の共通の元データ。
-/

@[expose] public section
universe u v u' v'
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable (D : Type u') [Category.{v'} D] (C : Type u) [Category.{v} C] [ModelCategory C]

abbrev pathEvaluation (n : ℕ) (i : Fin (n + 1)) : ComposableArrows C n ⥤ C :=
  (evaluation (Fin (n + 1)) C).obj i

structure Family (n m : ℕ) (X Y : C) where
  left : D ⥤ ComposableArrows C n
  right : D ⥤ ComposableArrows C m
  a : left ⋙ pathEvaluation C n 0 ⟶ (Functor.const D).obj X
  middle : right ⋙ pathEvaluation C m 0 ⟶ left ⋙ pathEvaluation C n (Fin.last n)
  b : (Functor.const D).obj Y ⟶ right ⋙ pathEvaluation C m (Fin.last m)
  a_mem : ∀ d, weakEquivalences C (a.app d)
  middle_mem : ∀ d, weakEquivalences C (middle.app d)
  b_mem : ∀ d, weakEquivalences C (b.app d)
  left_mem : ∀ {d d'} (f : d ⟶ d') i, weakEquivalences C ((left.map f).app i)
  right_mem : ∀ {d d'} (f : d ⟶ d') i, weakEquivalences C ((right.map f).app i)

namespace Family
variable {D C} {n m : ℕ} {X Y : C} (F : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family D C n m X Y)

def zigzagObj (d : D) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj (F.left.obj d) (F.right.obj d) (F.a.app d) (F.a_mem d)
    (F.middle.app d) (F.middle_mem d) (F.b.app d) (F.b_mem d)

end Family
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

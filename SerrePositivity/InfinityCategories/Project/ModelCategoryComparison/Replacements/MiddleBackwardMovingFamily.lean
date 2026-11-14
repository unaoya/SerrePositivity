module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardFamilyReplacementComparisons
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagram

/-!
# 動く局所端点を持つ元の左右ブロック図式

概要：局所端点を添字圏上の二つの評価関手とし、元の左右射列と三つの脚を保持する。
方針：固定端点の場合と同じ元のモデル圏の入力を、動く端点の自然変換で記録する。
規約：局所端点の全縦弱同値を保持し、定数図式とは仮定しない。
使われ方：任意の元の前後の語を保持する中央列の置換。
-/

@[expose] public section
universe u v u' v'
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra

variable (D : Type u') [Category.{v'} D] (C : Type u) [Category.{v} C] [ModelCategory C]

structure MovingFamily (n m : ℕ) (A B : D ⥤ C) where
  left : D ⥤ ComposableArrows C n
  right : D ⥤ ComposableArrows C m
  a : left ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C n 0 ⟶ A
  middle : right ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C m 0 ⟶ left ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C n (Fin.last n)
  b : B ⟶ right ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C m (Fin.last m)
  a_mem : ∀ d, weakEquivalences C (a.app d)
  middle_mem : ∀ d, weakEquivalences C (middle.app d)
  b_mem : ∀ d, weakEquivalences C (b.app d)
  left_mem : ∀ {d d'} (f : d ⟶ d') i, weakEquivalences C ((left.map f).app i)
  right_mem : ∀ {d d'} (f : d ⟶ d') i, weakEquivalences C ((right.map f).app i)
  endpoint_left_mem : ∀ {d d'} (f : d ⟶ d'), weakEquivalences C (A.map f)
  endpoint_right_mem : ∀ {d d'} (f : d ⟶ d'), weakEquivalences C (B.map f)

namespace MovingFamily
variable {D C} {n m : ℕ} {A B : D ⥤ C} (F : MovingFamily D C n m A B)

def zigzagObj (d : D) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) (A.obj d) (B.obj d) :=
  _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj (F.left.obj d) (F.right.obj d) (F.a.app d) (F.a_mem d)
    (F.middle.app d) (F.middle_mem d) (F.b.app d) (F.b_mem d)

end MovingFamily
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

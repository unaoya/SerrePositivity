module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedCutResidualLength

/-!
# 元の hammock の非指定文字列の長さによる切断の反復

概要：元の点に対する任意の依存型の構成を、空文字列と実際の一段の切断から再帰する。
方針：実際の nonemptyCut の残りの文字列の厳密な長さ減少を使う。
規約：端点は元の生成矢の終域へ移り、同じ残りの hammock の点を使う。
使われ方：反復した指定因子と生成矢の構成、およびその一意性。
-/

@[expose] public section
universe u s
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (Y : Paths C)
  (n : SimplexCategoryᵒᵖ)

open _root_.Classical in
def cutRec (P : ∀ X : Paths C, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n → Sort s)
    (base : ∀ X x, (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W X Y).app n x = [] → P X x)
    (step : ∀ X (x : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.NonemptyValue.space W X Y).obj n),
      P ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut W X Y).app n x).1.val.right ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut W X Y).app n x).2.2 → P X x.val)
    (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n) : P X x :=
  if hx : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W X Y).app n x = [] then base X x hx else
    step X ⟨x, hx⟩ (cutRec P base step
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut W X Y).app n ⟨x, hx⟩).1.val.right
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut W X Y).app n ⟨x, hx⟩).2.2)
termination_by ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W X Y).app n x).length
decreasing_by exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut_residual_length_lt W ⟨x, hx⟩

variable (P : ∀ X : Paths C, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n → Sort s)
  (base : ∀ X x, (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W X Y).app n x = [] → P X x)
  (step : ∀ X (x : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.NonemptyValue.space W X Y).obj n),
    P ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut W X Y).app n x).1.val.right ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut W X Y).app n x).2.2 → P X x.val)

lemma cutRec_empty (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n)
    (hx : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.colimitValue W X Y).app n x = []) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.cutRec W Y n P base step X x = base X x hx := by
  classical
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.cutRec, dite_eq_left hx]

lemma cutRec_nonempty (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.NonemptyValue.space W X Y).obj n) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.cutRec W Y n P base step X x.val = step X x
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.cutRec W Y n P base step ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut W X Y).app n x).1.val.right
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.nonemptyCut W X Y).app n x).2.2) := by
  classical
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.cutRec, dite_eq_right x.property]
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor

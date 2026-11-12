module

public import SerrePositivity.EInfinity.Hammock.UnmarkedCutResidualLength

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
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (Y : Paths C)
  (n : SimplexCategoryᵒᵖ)

open Classical in
def cutRec (P : ∀ X : Paths C, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n → Sort s)
    (base : ∀ X x, (colimitValue W X Y).app n x = [] → P X x)
    (step : ∀ X (x : (NonemptyValue.space W X Y).obj n),
      P ((nonemptyCut W X Y).app n x).1.val.right ((nonemptyCut W X Y).app n x).2.2 → P X x.val)
    (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n) : P X x :=
  if hx : (colimitValue W X Y).app n x = [] then base X x hx else
    step X ⟨x, hx⟩ (cutRec P base step
      ((nonemptyCut W X Y).app n ⟨x, hx⟩).1.val.right
      ((nonemptyCut W X Y).app n ⟨x, hx⟩).2.2)
termination_by ((colimitValue W X Y).app n x).length
decreasing_by exact nonemptyCut_residual_length_lt W ⟨x, hx⟩

variable (P : ∀ X : Paths C, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n → Sort s)
  (base : ∀ X x, (colimitValue W X Y).app n x = [] → P X x)
  (step : ∀ X (x : (NonemptyValue.space W X Y).obj n),
    P ((nonemptyCut W X Y).app n x).1.val.right ((nonemptyCut W X Y).app n x).2.2 → P X x.val)

lemma cutRec_empty (X : Paths C) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n)
    (hx : (colimitValue W X Y).app n x = []) :
    cutRec W Y n P base step X x = base X x hx := by
  classical
  rw [cutRec, dite_eq_left hx]

lemma cutRec_nonempty (X : Paths C) (x : (NonemptyValue.space W X Y).obj n) :
    cutRec W Y n P base step X x.val = step X x
      (cutRec W Y n P base step ((nonemptyCut W X Y).app n x).1.val.right
        ((nonemptyCut W X Y).app n x).2.2) := by
  classical
  rw [cutRec, dite_eq_right x.property]
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor

module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutCongr

/-!
# 元の射列の端点表示と固定切断の異種等式

概要：端点を含む射列の異種等式から、同じ生成矢での接頭射・残りを回収する。
方針：端点と射列の等式で帰納し、固定切断の一意性を使う。
規約：元の生成矢と全射列を保持する。
使われ方：語の圧縮した生の列と元の区間合成の切断の照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutHEq
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a : Quiver.Total C} {X Y X' Y' : C} {p : Quiver.Path X Y} {q : Quiver.Path X' Y'}
  (hX : X = X') (hY : Y = Y') (hpq : HEq p q)
  (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a p) (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a q)

include hX hY hpq in
lemma left_heq : HEq P.left Q.left := by
  cases hX
  cases hY
  have h := eq_of_heq hpq
  cases h
  exact heq_of_eq (congrArg (fun R => R.left) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedCut_ext W P Q))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutHEq (left_heq)


include hX hY hpq in
lemma right_heq : HEq P.right Q.right := by
  cases hX
  cases hY
  have h := eq_of_heq hpq
  cases h
  exact heq_of_eq (congrArg (fun R => R.right) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedCut_ext W P Q))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutHEq (right_heq)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutHEq

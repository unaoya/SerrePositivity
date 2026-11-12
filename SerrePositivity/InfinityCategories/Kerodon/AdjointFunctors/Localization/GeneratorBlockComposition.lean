module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockEquivalence

/-!
# 交互標準形の合成と元の射列との両立

概要：元の射列の連結を交互標準形へ移し、単位則と結合則を証明する。
方針：正規化と flatten の互いに逆な全単射を使い、元の連結の各法則を回収する。
規約：端点と全生成文字を保つ元の連結を使う。
使われ方：元の自由積の交互標準形を圏として使うための合成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockComposition
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

def comp {X Y Z : C} (N : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y) (M : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W Y Z) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalize W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W N).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W M))

lemma flatten_comp {X Y Z : C} (N : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y) (M : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W Y Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W (comp W N M) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W N).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flattenNormal W M) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flatten_normalize W _

lemma normalize_comp {X Y Z : C} (p : Quiver.Path X Y) (q : Quiver.Path Y Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalize W (p.comp q) = comp W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalize W p) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalize W q) := by
  simp only [comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.flatten_normalize]

lemma empty_comp {X Y : C} (N : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y) : comp W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.empty W X) N = N := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockEquivalence.flatten_injective W X Y
  rw [flatten_comp]
  exact Quiver.Path.nil_comp _

lemma comp_empty {X Y : C} (N : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y) : comp W N (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.empty W Y) = N := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockEquivalence.flatten_injective W X Y
  rw [flatten_comp]
  rfl

lemma comp_assoc {X Y Z T : C} (N : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W X Y) (M : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W Y Z) (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Normal W Z T) :
    comp W (comp W N M) P = comp W N (comp W M P) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockEquivalence.flatten_injective W X T
  simp only [flatten_comp, Quiver.Path.comp_assoc]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorBlockComposition

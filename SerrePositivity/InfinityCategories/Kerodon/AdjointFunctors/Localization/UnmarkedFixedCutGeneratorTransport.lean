module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCut

/-!
# 同じ元の生成矢の表示による固定切断の移送

概要：生成矢の等式で固定切断を移し、元の接頭射・残りの異種等式を保持する。
方針：生成矢の等式で帰納する。
規約：元の射列とその端点は保持する。
使われ方：圧縮後の各行の切断を元の生成矢へ揃える。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutGeneratorTransport
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Quiver.Total C} {X Y : C} {p : Quiver.Path X Y}

def changeGenerator (h : a = b) (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a p) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W b p := h ▸ P

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutGeneratorTransport (changeGenerator)


lemma changeGenerator_left (h : a = b) (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a p) :
    HEq (changeGenerator W h P).left P.left := by cases h; rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutGeneratorTransport (changeGenerator_left)


lemma changeGenerator_right (h : a = b) (P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut W a p) :
    HEq (changeGenerator W h P).right P.right := by cases h; rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutGeneratorTransport (changeGenerator_right)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutGeneratorTransport

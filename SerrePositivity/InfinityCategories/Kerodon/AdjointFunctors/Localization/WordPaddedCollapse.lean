module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardFixed
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPadding
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit
public import Mathlib.Tactic.FinCases

/-!
# 元の両端 padding と三列の語の回収

概要：一列 forward に両端 backward を付けた語を元の threeArrow と同定する。
方針：元の三列の向きを照合し、中央の合成を同じ語の射へ束ねる。
規約：同型類ではなく元の語の等式と元の射の自然性を提供する。
使われ方：forward 部分語図式の余極限から元の三本矢の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

lemma padding_single_forward : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.object_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow rfl
  intro i
  change Fin 3 at i
  fin_cases i <;> rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (padding_single_forward)


def paddedCollapse (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardCore a) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse a) ≫ eqToHom padding_single_forward

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddedCollapse)


lemma paddedCollapse_naturality {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap f) ≫ paddedCollapse b = paddedCollapse a := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap f) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse b) ≫ eqToHom padding_single_forward) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardCollapse_naturality]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddedCollapse_naturality)


def paddedCollapseNat : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardFunctor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor ⟶
    (Functor.const _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word).obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow where
  app := paddedCollapse
  naturality _ _ f := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardCore.forwardMap f) ≫ paddedCollapse _ = paddedCollapse _ ≫ 𝟙 _
    rw [Category.comp_id, paddedCollapse_naturality]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (paddedCollapseNat)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

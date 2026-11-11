module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# 元の有限頂点集合の包含による全指定相対関手

概要：元の部分集合の包含を元の自由圏の全指定相対関手へ束ねる。
方針：生成辺を保つ元の subsetFunctor を使う。
規約：quiver は両有限集合で局所選択する。
使われ方：有限部分木の hammock 図式の遷移。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] {S R : Finset Q}

def subsetRelative (h : S ⊆ R) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver R
    LocalizerMorphism (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)))
      (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex R))) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver R
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.subsetFunctor h, fun _ _ _ _ => trivial⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

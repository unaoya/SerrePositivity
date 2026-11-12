module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# 元の有限頂点自由圏から全自由圏への相対包含

概要：元の pathInclusion を全指定相対関手へ束ねる。
方針：元の生成辺と射列をそのまま射影する。
規約：quiver は有限頂点側だけ局所選択する。
使われ方：持ち上げた元の hammock grid の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q]

def pathRelative (S : Finset Q) : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    LocalizerMorphism (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)))
      (⊤ : MorphismProperty (Paths Q)) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S, fun _ _ _ _ => trivial⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

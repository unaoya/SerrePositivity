module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverGroupoidThin

/-!
# 元の根付き被覆の自由 groupoid の連結性

概要：元の任意の二頂点の間にはちょうど一つの groupoid の射がある。
方針：根からの実際の対称射列を評価し、薄さと合わせる。
規約：Unique は局所的に選べる定義とし、大域 instance は追加しない。
使われ方：元の被覆の木性と hammock の固定端点。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma root_groupoid_hom_nonempty (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Nonempty ((Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A) ⟶
      (Quiver.FreeGroupoid.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj x) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  obtain ⟨p⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.root_connected A x
  exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.symmetricEvaluation (Q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).map p⟩

lemma groupoid_hom_nonempty :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ x y : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A), Nonempty (x ⟶ y) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro x y
  obtain ⟨f⟩ := root_groupoid_hom_nonempty A x.as
  obtain ⟨g⟩ := root_groupoid_hom_nonempty A y.as
  exact ⟨inv f ≫ g⟩

@[instance_reducible] def groupoidHomUnique :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ x y : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A), Unique (x ⟶ y) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro x y
  exact { default := (groupoid_hom_nonempty A x y).some,
          uniq := fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoid_hom_unique A f _ }

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

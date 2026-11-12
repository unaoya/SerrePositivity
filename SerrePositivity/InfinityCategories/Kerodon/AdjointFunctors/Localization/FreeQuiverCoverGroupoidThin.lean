module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverGroupoidFaithful

/-!
# 元の根付き被覆の自由 groupoid の薄さ

概要：被覆の同じ二頂点の間の自由 groupoid の射は一意である。
方針：終点の式で射影を比較し、証明済みの忠実性を適用する。
規約：元の groupoid の全射を対象とし、薄さを入力にしない。
使われ方：被覆の木性と固定端点の hammock の持ち上げ。

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

lemma groupoid_hom_unique :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ {x y : Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)} (f g : x ⟶ y), f = g := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidProjection_faithful A
  intro x y f g
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidProjection A).map_injective
  apply (cancel_epi x.as.path).mp
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidProjection_endpoint A f).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidProjection_endpoint A g).symm

lemma groupoid_isThin : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A; Quiver.IsThin (Quiver.FreeGroupoid (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro x y
  exact ⟨fun f g => groupoid_hom_unique A f g⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

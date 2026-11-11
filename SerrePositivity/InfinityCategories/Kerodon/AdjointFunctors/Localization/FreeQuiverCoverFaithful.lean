module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftPaths

/-!
# 元の被覆の自由圏の関手の忠実性

概要：同じ始点を持つ元の二つの持ち上げ射列は基底の射列で一意に決まる。
方針：実際の持ち上げ終点を含む pathStar の単射性を適用する。
規約：元の自由圏の関手そのものの忠実性を証明する。
使われ方：元の可換正方形と全 hammock の縦射の持ち上げ。

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

lemma pathProjection_faithful : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A; (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).Faithful := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  refine ⟨?_⟩
  intro x y p q h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A at x y
  change @Quiver.Path (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A) x y at p q
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).mapPath p = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).mapPath q at h
  have he : (⟨y, p⟩ : Quiver.PathStar x) = ⟨y, q⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftPaths.lifted_pathStar_unique A x ⟨y, p⟩ ⟨y, q⟩ (congrArg (Sigma.mk y.base) h)
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

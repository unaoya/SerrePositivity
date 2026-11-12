module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeStrictNaturality
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanIntervalConeImageIsos
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerUnit

/-!
概要：元の左右の三角形と置換後の中心への比較の整合。
方針：strict な自然性の式の端点を揃え恒等後合成を除く。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {X Y Z : KanObject.{u}}
/-- 概要：元の左右の三角形と置換後の中心への比較の整合。
方針：strict な自然性の式の端点を揃え恒等後合成を除く。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma intervalPullbackConeLeftImageIso_triangle (f : X ⟶ Y) (g : Z ⟶ Y) :
    intervalPullbackConeTriangleIso f g (AsSmall.up.map WalkingCospan.Hom.inl) ≪≫
      intervalPullbackConeLeftImageIso f g =
    intervalPullbackConeCenterImageIso f g := by
  have h := intervalPullbackConeLegSectionIso_strict_naturality f g
    (AsSmall.up.map WalkingCospan.Hom.inl)
  change (intervalPullbackConeTriangleIso f g
      (AsSmall.up.map WalkingCospan.Hom.inl)).postcomp (𝟙 Y.obj) ≪≫
    functorEqIso _ ≪≫
      (intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.left)).postcomp
        (intervalReplacementEndpoint f) =
    intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.one) ≪≫ functorEqIso _ at h
  have hid := functorIso_postcomp_id
    (intervalPullbackConeTriangleIso f g (AsSmall.up.map WalkingCospan.Hom.inl))
  have h' := (congrArg (fun t ↦ t ≪≫ functorEqIso _ ≪≫
    (intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.left)).postcomp
      (intervalReplacementEndpoint f)) hid).symm.trans h
  exact functorIso_transport_image_square _ _ _ _ _ h'
/-- 概要：元の左右の三角形と置換後の中心への比較の整合。
方針：strict な自然性の式の端点を揃え恒等後合成を除く。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma intervalPullbackConeRightImageIso_triangle (f : X ⟶ Y) (g : Z ⟶ Y) :
    intervalPullbackConeTriangleIso f g (AsSmall.up.map WalkingCospan.Hom.inr) ≪≫
      intervalPullbackConeRightImageIso f g =
    intervalPullbackConeCenterImageIso f g := by
  have h := intervalPullbackConeLegSectionIso_strict_naturality f g
    (AsSmall.up.map WalkingCospan.Hom.inr)
  change (intervalPullbackConeTriangleIso f g
      (AsSmall.up.map WalkingCospan.Hom.inr)).postcomp (𝟙 Y.obj) ≪≫
    functorEqIso _ ≪≫
      (intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.right)).postcomp g =
    intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.one) ≪≫ functorEqIso _ at h
  have hid := functorIso_postcomp_id
    (intervalPullbackConeTriangleIso f g (AsSmall.up.map WalkingCospan.Hom.inr))
  have h' := (congrArg (fun t ↦ t ≪≫ functorEqIso _ ≪≫
    (intervalPullbackConeLegSectionIso f g (AsSmall.up.obj WalkingCospan.right)).postcomp g)
      hid).symm.trans h
  exact functorIso_transport_image_square_target _ _ _ _ _ pullback.condition.symm h'

end SerrePositivity.InfinityCategories.F2

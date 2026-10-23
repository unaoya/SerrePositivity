module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeStrictNaturality
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeImageIsos
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerUnit

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

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：元の左右の三角形と置換後の中心への比較の整合。
方針：strict な自然性の式の端点を揃え恒等後合成を除く。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma catPullbackConeLeftImageIso_triangle (p : A ⟶ C) (q : B ⟶ C) :
    catPullbackConeLegTriangleIso p q (AsSmall.up.map WalkingCospan.Hom.inl) ≪≫
      catPullbackConeLeftImageIso p q =
    catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.one) := by
  have h := catPullbackConeLegSectionIso_strict_naturality p q
    (AsSmall.up.map WalkingCospan.Hom.inl)
  change (catPullbackConeLegTriangleIso p q
      (AsSmall.up.map WalkingCospan.Hom.inl)).postcomp (𝟙 C) ≪≫
    functorEqIso _ ≪≫
      (catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.left)).postcomp
        (equivalencePathReplacementMap p) =
    catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.one) ≪≫ functorEqIso _ at h
  have hid := functorIso_postcomp_id
    (catPullbackConeLegTriangleIso p q (AsSmall.up.map WalkingCospan.Hom.inl))
  have h' := (congrArg (fun t ↦ t ≪≫ functorEqIso _ ≪≫
    (catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.left)).postcomp
      (equivalencePathReplacementMap p)) hid).symm.trans h
  exact functorIso_transport_square _ _ _ _ _ h'
/-- 概要：元の左右の三角形と置換後の中心への比較の整合。
方針：strict な自然性の式の端点を揃え恒等後合成を除く。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma catPullbackConeRightImageIso_triangle (p : A ⟶ C) (q : B ⟶ C) :
    catPullbackConeLegTriangleIso p q (AsSmall.up.map WalkingCospan.Hom.inr) ≪≫
      catPullbackConeRightImageIso p q =
    catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.one) := by
  have h := catPullbackConeLegSectionIso_strict_naturality p q
    (AsSmall.up.map WalkingCospan.Hom.inr)
  change (catPullbackConeLegTriangleIso p q
      (AsSmall.up.map WalkingCospan.Hom.inr)).postcomp (𝟙 C) ≪≫
    functorEqIso _ ≪≫
      (catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.right)).postcomp q =
    catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.one) ≪≫ functorEqIso _ at h
  have hid := functorIso_postcomp_id
    (catPullbackConeLegTriangleIso p q (AsSmall.up.map WalkingCospan.Hom.inr))
  have h' := (congrArg (fun t ↦ t ≪≫ functorEqIso _ ≪≫
    (catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.right)).postcomp q)
      hid).symm.trans h
  exact functorIso_transport_square _ _ _ _ _ h'

end SerrePositivity.InfinityCategories.F2

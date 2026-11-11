module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackConeStrictNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatPullbackConeImageIsos
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerUnit

/-!
概要：元の左右の三角形と置換後の中心への比較の整合。
方針：strict な自然性の式の端点を揃え恒等後合成を除く。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：元の左右の三角形と置換後の中心への比較の整合。
方針：strict な自然性の式の端点を揃え恒等後合成を除く。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma catPullbackConeLeftImageIso_triangle (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegTriangleIso p q (AsSmall.up.map WalkingCospan.Hom.inl) ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLeftImageIso p q =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.one) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegSectionIso_strict_naturality p q
    (AsSmall.up.map WalkingCospan.Hom.inl)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegTriangleIso p q
      (AsSmall.up.map WalkingCospan.Hom.inl)).postcomp (𝟙 C) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso _ ≪≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.left)).postcomp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.one) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso _ at h
  have hid := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_id
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegTriangleIso p q (AsSmall.up.map WalkingCospan.Hom.inl))
  have h' := (congrArg (fun t ↦ t ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso _ ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.left)).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p)) hid).symm.trans h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_transport_square _ _ _ _ _ h'
/-- 概要：元の左右の三角形と置換後の中心への比較の整合。
方針：strict な自然性の式の端点を揃え恒等後合成を除く。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma catPullbackConeRightImageIso_triangle (p : A ⟶ C) (q : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegTriangleIso p q (AsSmall.up.map WalkingCospan.Hom.inr) ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeRightImageIso p q =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.one) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegSectionIso_strict_naturality p q
    (AsSmall.up.map WalkingCospan.Hom.inr)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegTriangleIso p q
      (AsSmall.up.map WalkingCospan.Hom.inr)).postcomp (𝟙 C) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso _ ≪≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.right)).postcomp q =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.one) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso _ at h
  have hid := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_id
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegTriangleIso p q (AsSmall.up.map WalkingCospan.Hom.inr))
  have h' := (congrArg (fun t ↦ t ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso _ ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.catPullbackConeLegSectionIso p q (AsSmall.up.obj WalkingCospan.right)).postcomp q)
      hid).symm.trans h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_transport_square _ _ _ _ _ h'

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

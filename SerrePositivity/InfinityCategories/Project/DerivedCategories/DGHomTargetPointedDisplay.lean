module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomTargetCosliceComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleUnderlyingSpacePointed
/-!
概要：実 Hom 単位による coslice 比較を、同じ空間値 Hom 関手の pointed 表示へ送る。
方針：同じ基礎空間関手の始点固定 Tw 表示を前合成し、実射影の全単体等式を結ぶ。
規約：全 fiber の同値性は別工程。使われ方：F1 Hom 関手族との全比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] (x : C)
/-- 一般 dg 対象からの同じ R 加群値 Hom に基礎空間を適用した全関手。 -/
def dgHomTargetUnderlyingSpaceInfinity :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetModuleLift R C x)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R C

/-- 同じ実 Hom 単位から構成した、元の実 coslice 全体の pointed 表示。 -/
def dgHomTargetCoslicePointedDisplay :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVertexCoslice R C x) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCosliceComparison R C x) ≫
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnitVertex R C)) ≫
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpacePointedDisplay R C
/-- 同じ実 pointed 表示は、同じ基礎空間値 Hom 関手を底に持つ。 -/
lemma dgHomTargetCoslicePointedDisplay_projection :
    dgHomTargetCoslicePointedDisplay R C x ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).symm
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) ≫ dgHomTargetUnderlyingSpaceInfinity R C x := by
  rw [dgHomTargetCoslicePointedDisplay, Category.assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpacePointedDisplay_projection]
  simp only [← Category.assoc, ← Functor.map_comp]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_projection,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomTargetCosliceComparison_projection, Functor.map_comp, Category.assoc]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories

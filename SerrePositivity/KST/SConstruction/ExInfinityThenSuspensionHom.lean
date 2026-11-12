module
public import SerrePositivity.KST.SConstruction.ExInfinitySuspensionComparison
public import SerrePositivity.KST.SConstruction.PointedSSetSuspensionHom
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedSuspensionTransformation

/-! # 同じ Ex∞ の後の suspension が回収する通常射
概要：元の Ex∞ 点つき射の suspension を、同じ合成豊穣関手の全 Hom から回収する。
方針：元の点つき射の Ex∞ 回収と元の suspension 回収を合成する。
規約：元の円と射を変更しない。使われ方：隣接段 span の左脚の実成分。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 元の通常の点つき射を同じ Ex∞ で写し、元の円で suspension した実射。 -/
def exInfinityThenSuspensionMap {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    (coaugmentedThenSuspensionFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit).obj X ⟶
      (coaugmentedThenSuspensionFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit).obj Y :=
  PointedSimplicialSet.circle.{u} ◁ (exInfinityPointedKanMap f).hom

/-- 同じ合成豊穣関手の通常射は、元の Ex∞ 射の同じ suspension を回収する。 -/
lemma exInfinityThenSuspensionFunctor_hom {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    eHomEquiv SSet f ≫
      (coaugmentedThenSuspensionFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit).map X Y =
      eHomEquiv SSet (exInfinityThenSuspensionMap f) := by
  change eHomEquiv SSet f ≫
    (exInfinityPointedEnrichedFunctor.map X Y ≫
      pointedSSetSuspensionEnrichedFunctor.map _ _) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ pointedSSetSuspensionEnrichedFunctor.map _ _)
      (coaugmentedPointedEnrichedFunctor_hom
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit f)).trans
        (pointedSSetSuspensionEnrichedFunctor_hom
          (coaugmentedPointedMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit f)))

end SerrePositivity.KST.SConstruction

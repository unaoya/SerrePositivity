module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LeftFibrationConeInvariance
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseLimits
/-!
概要：像の実錐の持ち上げを、持ち上げた元の錐の像へ同定して切断制限を比較する。
方針：同じ join の宇宙同型と、錐の値の厳密な後合成公式を使う。
規約：図式の固定条件を保つ。使われ方：Hom 試験の全関手同型を native 錐へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
/-- 同じ native 錐の宇宙持ち上げと後合成の比較。 -/
lemma JoinCone.ulift_mapJoinCone_val {K X Y : SSet.{u}} (F : X ⟶ Y)
    {d : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone d) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F c)).val =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).val ≫ (SSet.uliftFunctor.{u + 1, u}).map F := by
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, u + 1} K 0).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (c.val ≫ F) =
    ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, u + 1} K 0).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map c.val) ≫ (SSet.uliftFunctor.{u + 1, u}).map F
  rw [Functor.map_comp, Category.assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.JoinCone (ulift_mapJoinCone_val)

/-- 同じ native 錐の宇宙持ち上げと後合成の比較。 -/
lemma leftFibrationConeRestriction_ulift_postcomp_iff
    {K X Y : SSet.{u}} {E B : SSet.{u + 1}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (F : X ⟶ Y)
    (H : (SSet.uliftFunctor.{u + 1, u}).obj Y ⟶ B)
    {d : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftFibrationConeRestriction p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone H (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F c)))) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftFibrationConeRestriction p
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone ((SSet.uliftFunctor.{u + 1, u}).map F ≫ H)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.leftFibrationConeRestriction_isQCatEquivalence_iff_pre,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.leftFibrationConeRestriction_isQCatEquivalence_iff_pre]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F c)).val ≫ H) _) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).val ≫ ((SSet.uliftFunctor.{u + 1, u}).map F ≫ H)) _)
  rw [JoinCone.ulift_mapJoinCone_val, Category.assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories

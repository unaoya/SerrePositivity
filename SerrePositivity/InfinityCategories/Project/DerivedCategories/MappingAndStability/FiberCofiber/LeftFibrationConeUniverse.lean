module
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.LiftedConePointedRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportConeRestriction
/-!
概要：元の全錐の切断制限を、持ち上げた native 錐と分類図式の同じ制限へ移す。
方針：元の相対関手の宇宙同型と join の形状同型を、両方向で消去する。
規約：極限錐の選択を変えない。使われ方：dg Hom 試験の極限判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet
open scoped _root_.Simplicial
/-- 元の全錐の実切断制限の宇宙比較。 -/
lemma leftFibrationConeRestriction_ulift_iff
    {K E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] {d : K ⟶ B} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftFibrationConeRestriction p c) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftFibrationConeRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map p) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) := by
  let g := Over.homMk (U := Over.mk d) (V := Over.mk c.val)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K) c.property
  let e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedConeShapeOverIso c
  let ep : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace ((SSet.uliftFunctor.{u + 1, u}).map p)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).val ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace ((SSet.uliftFunctor.{u + 1, u}).map p)
      ((SSet.uliftFunctor.{u + 1, u}).map c.val) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverFunctor ((SSet.uliftFunctor.{u + 1, u}).map p)).mapIso e.op
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre
      ((SSet.uliftFunctor.{u + 1, u}).map p) e.hom) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso ep).isQCatEquivalence
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftFibrationConeRestriction ((SSet.uliftFunctor.{u + 1, u}).map p)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre ((SSet.uliftFunctor.{u + 1, u}).map p) e.hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre ((SSet.uliftFunctor.{u + 1, u}).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.uliftOverMorphism g) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftFibrationConeRestriction_eq_overPre,
      ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.liftedConeShapeOverIso_restriction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_comp]
  rw [hn, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.leftFibrationConeRestriction_eq_overPre]
  constructor
  · intro h
    exact he.comp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorOverPre_isQCatEquivalence_ulift p g h)
  · intro h
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.relativeFunctorOverPre_isQCatEquivalence_of_ulift p g (he.cancel_left h)
/-- 元の全錐の実切断制限の宇宙比較。 -/
lemma LeftTransportRepresentation.uliftConeRestriction_iff
    {K E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
    {d : K ⟶ B} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftFibrationConeRestriction p c) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftFibrationConeRestriction _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone R.diagram (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c))) :=
  (leftFibrationConeRestriction_ulift_iff p c).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation.coneRestriction_iff
      ((SSet.uliftFunctor.{u + 1, u}).map p) R (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.LeftTransportRepresentation (uliftConeRestriction_iff)

end SerrePositivity.InfinityCategories.Project.DerivedCategories

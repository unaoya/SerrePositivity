module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSourcePresentation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagramEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibrationTerminalRepresentation
/-!
概要：実 loop cospan の全錐の点上 slice による表示。
方針：元の相対境界充填と right fibration の表現を実射へ接続する。
規約：安定性や有限余極限を仮定しない。使われ方：HA 1.4.2.27 の余錐比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
lemma loopSquare_pullbackCone_vertex {X : SSet.{u}} {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square).vertex = t.vertex := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (horn 2 2 : SSet.{u}) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ t.square)) = t.vertex
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cospanConeSquareIso_initialPoint,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl
lemma loopCospan_coneRepresentation_exists {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) :
    ∃ f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm t.vertex),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f ∧ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.roofTerminalRepresentation_exists (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square) t.isPullback
  change (∃ f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone t.square).vertex),
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f ∧ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square)) at h
  rw [loopSquare_pullbackCone_vertex] at h
  exact h
def loopCospanConeRepresentation {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm t.vertex) :=
  Classical.choose (loopCospan_coneRepresentation_exists t)
lemma loopCospanConeRepresentation_isQCatEquivalence {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (loopCospanConeRepresentation t) :=
  (Classical.choose_spec (loopCospan_coneRepresentation_exists t)).1
lemma loopCospanConeRepresentation_over {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopSquare y) :
    loopCospanConeRepresentation t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan t.square) :=
  (Classical.choose_spec (loopCospan_coneRepresentation_exists t)).2
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

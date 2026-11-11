module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndArrowTargetUnderCocone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.LiftedShapeFilteredCriterion
/-!
概要：元の指定終点図式の下の実評価 comma は、任意の有限形状に対して filtered。
方針：指定変換を持つ元の試験族への余錐を、全ての大きい有限試験形状へ戻す。
規約：元の評価写像と全族を保持し、Kan 性を要求しない。
使われ方：終点評価の Quillen A における coslice の弱可縮性。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
local notation "E" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.diagramCommaEvaluation κ D (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
/-- 概要：終点評価の実引き戻しの任意の小さい試験族に、元の全族への余錐が存在する。
方針：元の相対余錐を回収する。規約：指定値を保持。使われ方：終点評価の cofinal 性。 -/
lemma nonempty_indArrowTargetEvaluationComma_cocone {A L : SSet.{u}}
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ A) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) E) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) := by
  have h : (q ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) E) ≫ E =
      (q ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) E) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.nonempty_indArrowTargetUnder_cocone κ D hA hL z
    (q ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) E)
    (q ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) E) h
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily E z (q ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) E)
      (q ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) E) h = q := by
    apply pullback.hom_ext <;> simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.relativeCommaFamily, pullback.lift_fst,
      pullback.lift_snd]
  exact hq ▸ hc
/-- 概要：指定した κ-small な終点図式下の元の評価 comma は filtered。
方針：元の相対余錐を回収する。規約：指定値を保持。使われ方：終点評価の cofinal 性。 -/
lemma indArrowTargetEvaluationComma_isFiltered {L : SSet.{u}} (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z) E) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isFilteredInfinity_of_liftedShape_cocones (Fact.out : κ.IsRegular)
  intro A hA q
  exact nonempty_indArrowTargetEvaluationComma_cocone κ D hA hL z q
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

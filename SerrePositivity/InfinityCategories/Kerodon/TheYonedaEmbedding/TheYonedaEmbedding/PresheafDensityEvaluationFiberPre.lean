module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafDensityRestrictedValuePre

/-!
概要：同じ評価余錐の実際の fiber 値写像は、必要な持ち上げた Kan 標的への前合成同値を持つ。
方針：同じ評価復元射の前合成同値を、元の値写像との関手同型から消去する。
規約：同じ native な余錐と実際の fiber 写像を使う。
使われ方：元の評価余錐の余極限性の検査。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (x : C _⦋0⦌)

/-- 同じ評価復元射の持ち上げは、持ち上げた小さい Kan 標的への前合成同値。 -/
lemma presheafDensityEvaluationReconstructionLift_pre (Z : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationReconstructionLift F x)).app
        ((SSet.uliftFunctor.{u + 1, u}).obj Z)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationReconstructionLift, pre_map, NatTrans.comp_app]
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationDiagram F x)))
      ((SSet.uliftFunctor.{u + 1, u}).obj Z)).isSimplicialHomotopyEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ulift_pre_homotopyEquivalence _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.isSimplicialHomotopyEquivalence
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationReconstruction_isPrecompositionEquivalence F x) Z)))

/-- 同じ元の評価変換の実際の fiber 値写像への前合成は、必要な標的で同値。 -/
lemma presheafDensityEvaluatedFiberMap_pre (Z : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluatedFiberMap F x)).app
        ((SSet.uliftFunctor.{u + 1, u}).obj Z)) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationValueComparisonIso F x).map_pre
    ((SSet.uliftFunctor.{u + 1, u}).obj Z)
  have hq := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityRestrictedGlobalValueMap_pre F x Z).isQCatEquivalence
  have hc := (hq.ofFunctorIso he.symm).isSimplicialHomotopyEquivalence
  rw [pre_map, NatTrans.comp_app] at hc
  exact (presheafDensityEvaluationReconstructionLift_pre F x Z).cancel_right hc

/-- 同じ native 評価余錐の実際の fiber 値写像も、必要な標的への前合成で同値。 -/
lemma presheafDensityEvaluationCoconeFiberValueMap_pre (Z : SSet.{u}) [KanComplex Z] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeFiberValueMapAt (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationCocone F x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationVertex F x) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationCocone_vertex F x))).app
          ((SSet.uliftFunctor.{u + 1, u}).obj Z)) := by
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityEvaluationFiberIso F x).map_pre
    ((SSet.uliftFunctor.{u + 1, u}).obj Z)
  have hq := (presheafDensityEvaluatedFiberMap_pre F x Z).isQCatEquivalence
  exact (hq.ofFunctorIso he.symm).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

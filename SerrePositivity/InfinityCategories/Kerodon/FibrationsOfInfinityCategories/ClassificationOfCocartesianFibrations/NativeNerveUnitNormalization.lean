module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativeNerveStraighteningComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationComparisonCoherence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportRepresentationSelfComparison

/-! 同じ表現空間の比較の自己単位則で、元の全native単位を正規化する。 -/

@[expose] public section
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance kanDiagramSelf_kan {C : Type u} [Category.{u} C]
    (F : C ⥤ KanObject.{u}) (c : C) : KanComplex ((F ⋙ kanObjectForget).obj c) :=
  (F.obj c).isKanComplex

/-- 元の指定比較の自己単位・合成・評価の法則。 -/
lemma leftStraighteningInfinityDiagram_nerveCandidateIso_normalized {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    leftStraighteningInfinityDiagram_nerveCandidateIso p =
      leftStraighteningInfinityDiagram_representationIso p (nerveLeftTransportRepresentation p) ≪≫
        (leftStraighteningCoherentMap_oppositeVertexIso p).symm := by
  unfold leftStraighteningInfinityDiagram_nerveCandidateIso
  rw [nerveStraighteningRepresentationIso_self]

/-- 元の指定比較の自己単位・合成・評価の法則。 -/
lemma weightedNerveNativeStraighteningUnitIso_normalized {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    weightedNerveNativeStraighteningUnitIso F =
      weightedNerveStraighteningUnitIso F ≪≫
        leftStraighteningCoherentMap_oppositeVertexIso (weightedNerveProjection (F ⋙ kanObjectForget)) ≪≫
        (leftStraighteningInfinityDiagram_representationIso
          (weightedNerveProjection (F ⋙ kanObjectForget))
          (nerveLeftTransportRepresentation (weightedNerveProjection (F ⋙ kanObjectForget)))).symm := by
  unfold weightedNerveNativeStraighteningUnitIso
  rw [leftStraighteningInfinityDiagram_nerveCandidateIso_normalized]
  simp only [Iso.trans_symm]
  rfl

/-- 元の指定比較の自己単位・合成・評価の法則。 -/
lemma weightedNerveNativeStraighteningUnitIso_trans_representationIso {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) :
    weightedNerveNativeStraighteningUnitIso F ≪≫
      leftStraighteningInfinityDiagram_representationIso
        (weightedNerveProjection (F ⋙ kanObjectForget))
        (nerveLeftTransportRepresentation (weightedNerveProjection (F ⋙ kanObjectForget))) =
    weightedNerveStraighteningUnitIso F ≪≫
      leftStraighteningCoherentMap_oppositeVertexIso (weightedNerveProjection (F ⋙ kanObjectForget)) := by
  rw [weightedNerveNativeStraighteningUnitIso_normalized]
  simp [Iso.trans_assoc]

/-- 元の指定比較の自己単位・合成・評価の法則。 -/
lemma weightedNerveNativeStraighteningUnitIso_representation_evaluate {C : Type u} [Category.{u} C] (F : C ⥤ KanObject.{u}) (c : C) :
    functorHomEvaluate (weightedNerveNativeStraighteningUnitIso F).hom
        (ULift.up (nerveVertex c)) ≫
      functorHomEvaluate (leftStraighteningInfinityDiagram_representationIso
        (weightedNerveProjection (F ⋙ kanObjectForget))
        (nerveLeftTransportRepresentation (weightedNerveProjection (F ⋙ kanObjectForget)))).hom
        (ULift.up (nerveVertex c)) =
    functorHomEvaluate (weightedNerveStraighteningUnitIso F).hom (ULift.up (nerveVertex c)) ≫
      functorHomEvaluate (leftStraighteningCoherentMap_oppositeVertexIso
        (weightedNerveProjection (F ⋙ kanObjectForget))).hom (ULift.up (nerveVertex c)) := by
  have h := congrArg (fun e : FunctorIso (kanDiagramCoherentNerve F)
      (leftCoherentTransport (weightedNerveProjection (F ⋙ kanObjectForget))) =>
        functorHomEvaluate e.hom (ULift.up (nerveVertex c))) (weightedNerveNativeStraighteningUnitIso_trans_representationIso F)
  simpa only [Iso.trans_hom, functorHomEvaluate_comp] using h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

end

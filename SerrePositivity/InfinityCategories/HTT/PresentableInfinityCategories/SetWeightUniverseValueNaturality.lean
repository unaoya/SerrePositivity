module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetSections
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SmallUnstraighteningValueTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.SpaceEdgeTransportValue
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FamilyEquivalenceReflection

/-!
概要：G8 の元の宇宙変更の値比較と、同じ指定辺の値の作用の全族自然性。
方針：普遍的な pointed space の fiber と同じ復元射の値比較を経由する。
規約：正本の spaceUniverseValueEquivalence の選択を保持する。
使われ方：G8 の四角形②の宇宙変更の因子。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open IsomorphismsAndIsofibrations Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors

namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：元の宇宙変更の値比較は、同じ小さい分類図式の値の作用と全族で可換。
方針：指定 fiber 比較の上で二つの輸送の自然性を合成し、同じ同値で反映する。
規約：宇宙の持ち上げと値比較の実射を保持する。
使われ方：G8 の後段の宇宙変更の自然性。 -/
def setWeightUniverseValue_edgeIso {x y : SpaceInfinity.{u} _⦋0⦌}
    (e : SpaceInfinity.{u}.Edge x y) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (spaceInfinityEdgeValue e) ≫
        (SetWeight.spaceUniverseValueEquivalence y).hom)
      ((SetWeight.spaceUniverseValueEquivalence x).hom ≫ spaceInfinityEdgeValue
        ((SSet.Edge.ofTruncated (uliftTruncatedEdge.{u + 1, u + 2} e)).map spaceUniverseDiagram)) := by
  let p := pointedSpaceProjection.{u}
  let G := leftStraighteningInfinityDiagram p
  let r := leftStraighteningInfinityReconstruction p
  let hr := leftStraighteningInfinityReconstruction_projection p
  let P := fun z : SpaceInfinity.{u} _⦋0⦌ => pointedSpaceFiberValueEquivalence z
  let Q := fun z : SpaceInfinity.{u} _⦋0⦌ =>
    vertexFiberMap p (smallLeftUnstraighteningProjection G) r hr z ≫
      (smallLeftUnstraighteningFiberValueEquivalence G z).hom
  let T := edgeTransport p e
  let w := spaceInfinityEdgeValue
    ((SSet.Edge.ofTruncated (uliftTruncatedEdge.{u + 1, u + 2} e)).map spaceUniverseDiagram)
  have hx : (SetWeight.spaceUniverseValueEquivalence x).hom = (P x).inv ≫ Q x := rfl
  have hy : (SetWeight.spaceUniverseValueEquivalence y).hom = (P y).inv ≫ Q y := rfl
  have h₁ := FunctorIso.postcomp (spaceInfinityEdgeTransportValueIso e)
    (SetWeight.spaceUniverseValueEquivalence y).hom
  simp only [hy, Category.assoc] at h₁
  have h₂ := FunctorIso.precomp (FunctorIso.postcomp (P y).homInvIso (Q y)) T
  have h₃ : FunctorIso (T ≫ Q y) (Q x ≫ w) :=
    smallUnstraighteningFiberMapValue_transportIso p G r hr e
  have h₄ := FunctorIso.postcomp (P x).homInvIso (Q x ≫ w)
  simp only [Category.assoc, Category.id_comp] at h₂ h₄
  apply functorIsoOfPrecompEquivalence (P x).hom (P x).isQCatEquivalence
  rw [hx, hy]
  simp only [Category.assoc]
  exact h₁ ≪≫ h₂ ≪≫ h₃ ≪≫ h₄.symm

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

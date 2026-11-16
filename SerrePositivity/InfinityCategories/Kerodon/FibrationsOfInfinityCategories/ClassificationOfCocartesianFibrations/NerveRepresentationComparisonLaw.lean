module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RepresentationComparisonCoherence

/-!
概要：通常のnerve上で元の分類比較は、同じ表現空間内の指定比較との合成を保つ。
方針：既存のdiagramIsoの合成則と、同じ可縮な表現空間での同型の一意性を使う。
規約：Kerodon §5.6（Tag 027M）、HTT §3.3.2の既存構成の比較の合成則。
使われ方：S8 の元の指定分類比較を初頂点上で照合する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元のnerve分類比較に同じ表現空間内の比較を続けると、元の直接比較に一致する。 -/
lemma nerveCoherentTransportRepresentationIso_comp_diagramIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}} (p : E ⟶ nerve C) [LeftFibration p]
    (R S : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
    (a : VertexIso (transportWitnessVertex R) (transportWitnessVertex S)) :
    nerveCoherentTransportRepresentationIso p R ≪≫ R.diagramIso S a =
      nerveCoherentTransportRepresentationIso p S := by
  letI (n : SimplexCategoryᵒᵖ) :
      Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj E).obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (E.obj n)))
  unfold nerveCoherentTransportRepresentationIso smallFiberTransportRepresentationDiagramIso
  rw [← LeftTransportRepresentation.diagramIso_trans]
  apply congrArg (fun h => (nerveLeftTransportRepresentation p).diagramIso S h)
  exact smallFiberTransportRepresentationVertexIso_unique
    ((SSet.uliftFunctor.{u + 1, u}).map p) (hasSmallSimplexFibers_of_small_total _)
    (nerveLeftTransportRepresentation p) S _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

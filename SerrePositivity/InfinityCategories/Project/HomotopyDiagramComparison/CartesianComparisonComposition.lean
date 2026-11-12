module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PrismSquareComposition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CartesianPrismComparison

/-!
概要：元の同じ単位・左右輸送・比較正方形から、単位成分の合成式を回収。
方針：元の辺と正方形を保持して、標準の写像空間比較へ移す。
規約：元の cf 置換との比較と一般 coherent 極限保存は別工程。使われ方：HTT 5.2.4.6。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 同じ元の比較正方形から、単位成分と右輸送の合成が左輸送に一致することを導く。 -/
lemma cartesianComparison_component_comp {X Y E : SSet.{u}} [Quasicategory E]
    (F : X ⟶ Y) (G : Y ⟶ X) (i : X ⟶ E) (j : Y ⟶ E)
    (η : (Δ[1] : SSet.{u}) ⊗ X ⟶ X)
    (hη0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 X ≫ η = 𝟙 X) (hη1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X ≫ η = F ≫ G)
    (HL : (Δ[1] : SSet.{u}) ⊗ X ⟶ E)
    (hL0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 X ≫ HL = i) (hL1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X ≫ HL = F ≫ j)
    (HR : (Δ[1] : SSet.{u}) ⊗ Y ⟶ E)
    (hR0 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Y ≫ HR = G ≫ i) (hR1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Y ≫ HR = j)
    (J : (Δ[1] : SSet.{u}) ⊗ ((Δ[1] : SSet.{u}) ⊗ X) ⟶ E)
    (hηi : η ≫ i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ J)
    (hJb : ((Δ[1] : SSet.{u}) ◁ ((boundary 1).ι ▷ X)) ≫ J =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cartesianComparisonBoundary HL (((Δ[1] : SSet.{u}) ◁ F) ≫ HR))
    (hJ1 : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ J = HL) (x : X _⦋0⦌) :
    (hoFunctor.map i).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism η hη0 hη1))) x) ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism HR hR0 hR1)))
        (F.app (Opposite.op ⦋0⦌) x) =
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism HL hL0 hL1))) x := by
  let Hu := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism η hη0 hη1
  let Hr := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism HR hR0 hR1
  let Hl := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.homotopyOfPrism HL hL0 hL1
  have hzero : ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 X) ≫ J = snd Δ[1] X ≫ i := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 0, whiskerLeft_comp, Category.assoc, hJb,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cartesianComparisonBoundary_zero, hL0]
  have hone : ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) ≫ J =
      ((Δ[1] : SSet.{u}) ◁ F) ≫ HR := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryEndpoint_ι 1, whiskerLeft_comp, Category.assoc, hJb,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.cartesianComparisonBoundary_one]
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.prismSquareAt_component_comp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp Hu i)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp Hr F) Hl J hzero ?_ ?_ ?_ x
  · rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomEvaluate_homotopy_postcomp, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom,
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_precomp] at h
    exact h
  · exact hone
  · exact hηi.symm
  · exact hJ1

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

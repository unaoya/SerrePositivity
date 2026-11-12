module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.CoherentFilteredTotalDetection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.FilteredLeftFibrationHomotopyDetection

/-!
概要：coherent 全空間への有限射のホモトピー類を、元の値の類で表す。
方針：公開の有限値検出を内部 Hom の π₀ に降ろす。
規約：基点固定の正次数判定とは区別し、任意の有限試験複体について主張する。
使われ方：π₀ の代表元検出と、正次数の相対検出に必要な有限台。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
variable {B : SSet.{u}} [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]

/-- 有限試験複体から全空間へのホモトピー類は、一つの元の値に代表を持つ。 -/
lemma finite_mappingClass_value_representative
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    {K : SSet.{u}} [K.Finite] (a : π₀ ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F))) :
    ∃ b : B _⦋0⦌,
      ∃ t : π₀ ((ihom K).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) (ULift.up b))).obj),
        mapπ₀ ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentDiagramValueToTotalKan F b)) t = a := by
  obtain ⟨v, rfl⟩ := π₀.mk_surjective a
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F)).surjective v
  obtain ⟨b, g, h⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentFilteredTotalKan_finite_value_detection F f
  refine ⟨b, π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g), ?_⟩
  change π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.coherentDiagramValueToTotalKan F b)) =
    π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr h).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

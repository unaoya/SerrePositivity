module
public import SerrePositivity.KST.Fibration.VerdierFullSLowerCanonicalTriangle
public import SerrePositivity.KST.Fibration.StableCoreSingleKanHom

/-!
概要：指定下側の標準合成二胞体の短辺を、元の実 Kan 包含・商の射データへ厳密に戻す。
方針：最大化の実短辺公式を Yoneda で読み、同じ全 S• の辺と通常の射の復元を使う。
規約：短辺の端点と射を一緒に保持する。上側との共有対角の照合は別工程。
使われ方：K-6 c4 の商核の元の二射列への標準下側二胞体の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 同じ最大化の第一辺は、元の実 Kan 包含の同じ全一単体。 -/
theorem verdierFullSLowerCanonical_first_edge :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 2 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (stableCoreSingleKanMap d.inclusion)).edge := by
  have h := congrArg SSet.yonedaEquiv (verdierFullSLowerMaximalization_inclusion d)
  have h' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 2 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).edge := by
    simpa only [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_symm_comp,
      Equiv.apply_symm_apply] using! h
  exact h'.trans (stableMultiSingleKan_edge d.inclusion)

/-- 同じ最大化の第二辺は、元の実 Kan 商射の同じ全一単体。 -/
theorem verdierFullSLowerCanonical_last_edge :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (stableCoreSingleKanMap d.projection)).edge := by
  have h := congrArg SSet.yonedaEquiv (verdierFullSLowerMaximalization_projection d)
  have h' : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).edge := by
    simpa only [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv_symm_comp,
      Equiv.apply_symm_apply] using! h
  exact h'.trans (stableMultiSingleKan_edge d.projection)

/-- 同じ標準下側二胞体の第一辺の全射データは、元の実 Kan 包含そのもの。 -/
theorem verdierFullSLowerCanonical_first_data :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 2 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d))) =
    ⟨stableCoreSingleKanEnrichedFunctor.obj (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left),
      stableCoreSingleKanEnrichedFunctor.obj (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.middle),
      stableCoreSingleKanMap d.inclusion⟩ :=
  (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (verdierFullSLowerCanonical_first_edge d)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow (stableCoreSingleKanMap d.inclusion))

/-- 同じ標準下側二胞体の第二辺の全射データは、元の実 Kan 商射そのもの。 -/
theorem verdierFullSLowerCanonical_last_data :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.δ 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization (verdierFullSLowerSimplex d))) =
    ⟨stableCoreSingleKanEnrichedFunctor.obj (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.middle),
      stableCoreSingleKanEnrichedFunctor.obj (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right),
      stableCoreSingleKanMap d.projection⟩ :=
  (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (verdierFullSLowerCanonical_last_edge d)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow (stableCoreSingleKanMap d.projection))

end SerrePositivity.KST.Fibration

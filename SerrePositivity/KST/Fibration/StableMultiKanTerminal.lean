module
public import SerrePositivity.KST.Fibration.ZeroCategorySRealization
public import SerrePositivity.KST.Fibration.StableBoundaryKanComparison
public import SerrePositivity.KST.Fibration.KanTerminalComparison
public import SerrePositivity.KST.Fibration.QuotientSKernelTerminalCorner

/-! # 元の Verdier 四角形の正反復実現の角の終対象性と、同じ商核の角との比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open scoped Simplicial
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction

open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 零の安定入力の元の正反復実現の Ex∞ Kan 値は、空間の ∞ 圏の終対象である。 -/
theorem stableMultiKanVertex_isTerminal_of_zero (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (hC : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((stableMultiKanEnrichedFunctor r).obj C)) := by
  let V := (multiRealizationFunctor (r + 1)).obj (stableCategoryModel C)
  have hV : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit V)) :=
    multiRealization_toPoint_localized_isIso_of_allZero (r + 1) (stableCategoryModel C) hC
  have hi : IsIso (terminal.from (𝟙_ SSet.{u})) :=
    isIso_of_isTerminal isTerminalTensorUnit terminalIsTerminal _
  have he : toUnit V ≫ terminal.from (𝟙_ SSet.{u}) = terminal.from V :=
    terminal.hom_ext _ _
  apply exInfinityVertex_isTerminal_of_localized_toPoint V
  rw [← he, CategoryTheory.Functor.map_comp]
  infer_instance

/-- 元の指定 Verdier 四角形の零角は、同じ全正反復実現でも終対象に写る。 -/
theorem verdierMultiKanSquare_corner_isTerminal (r : ℕ) (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex
      (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor r)) 0 1) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex d.square 0 1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor r)).app (Opposite.op ⦋0⦌) z)
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor r)).app
      (Opposite.op ⦋0⦌) z =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((stableMultiKanEnrichedFunctor r).obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject z)) :=
    (congrArg (fun t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋0⦌ =>
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor r)).app (Opposite.op ⦋0⦌) t)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableVertex_object z).symm).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_vertex _ _)
  exact he.symm ▸ stableMultiKanVertex_isTerminal_of_zero r (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject z) d.zero_corner

/-- 元の一回の実現の両四角形の同じ角は、実際の終対象間の同型で比較される。 -/
def quotientSKernelCornerIso_verdierSingle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (quotientSKernelInfinitySquare d.inclusion d.projection) 0 1)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (d.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stableMultiKanEnrichedFunctor 0)) 0 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso (quotientSKernelInfinitySquare_corner_isTerminal d.isVerdier)
    (verdierMultiKanSquare_corner_isTerminal 0 d)

end SerrePositivity.KST.Fibration

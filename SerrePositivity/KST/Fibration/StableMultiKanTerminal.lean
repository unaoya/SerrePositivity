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
open SerrePositivity.KST.Comparison
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 零の安定入力の元の正反復実現の Ex∞ Kan 値は、空間の ∞ 圏の終対象である。 -/
theorem stableMultiKanVertex_isTerminal_of_zero (r : ℕ) (C : StableQCat.{u})
    (hC : IsZeroCategory C) :
    IsTerminalVertex (coherentNerveVertex ((stableMultiKanEnrichedFunctor r).obj C)) := by
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
theorem verdierMultiKanSquare_corner_isTerminal (r : ℕ) (d : VerdierDiagram.{u}) :
    IsTerminalVertex (squareVertex
      (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor r)) 0 1) := by
  let z := squareVertex d.square 0 1
  change IsTerminalVertex
    ((coherentNerveMap (stableMultiKanEnrichedFunctor r)).app (Opposite.op ⦋0⦌) z)
  have he : (coherentNerveMap (stableMultiKanEnrichedFunctor r)).app
      (Opposite.op ⦋0⦌) z =
      coherentNerveVertex ((stableMultiKanEnrichedFunctor r).obj (stableObject z)) :=
    (congrArg (fun t : StableInfinity.{u} _⦋0⦌ =>
      (coherentNerveMap (stableMultiKanEnrichedFunctor r)).app (Opposite.op ⦋0⦌) t)
        (stableVertex_object z).symm).trans (coherentNerveMap_vertex _ _)
  exact he.symm ▸ stableMultiKanVertex_isTerminal_of_zero r (stableObject z) d.zero_corner

/-- 元の一回の実現の両四角形の同じ角は、実際の終対象間の同型で比較される。 -/
def quotientSKernelCornerIso_verdierSingle (d : VerdierDiagram.{u}) :
    VertexIso (squareVertex (quotientSKernelInfinitySquare d.inclusion d.projection) 0 1)
      (squareVertex (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)) 0 1) :=
  terminalVertexIso (quotientSKernelInfinitySquare_corner_isTerminal d.isVerdier)
    (verdierMultiKanSquare_corner_isTerminal 0 d)

end SerrePositivity.KST.Fibration

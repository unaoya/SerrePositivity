module
public import SerrePositivity.KST.SConstruction.PerfectVerdierSequence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagrams

/-! # Cat^perf の実 coherent Verdier 四角形
概要：実商と冪等完備化を持つ列を、同じ二辺と零角を保持する全四角形で提示する。
方針：Cat^perf 内の実単体的写像を保持し、包含後の二辺を元の完全関手で固定する。
規約：四辺だけのホモトピー圏の等号で代用しない。使われ方：非連結 K の局所化性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 冪等完備化後の実右射を含む Cat^perf の coherent な Verdier 図式。 -/
structure PerfectVerdierDiagram extends PerfectVerdierSequence.{u} where
  square : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ perfectStableInfinity.{u}
  left_eq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex square 0 0 = toPerfectVerdierSequence.leftVertex
  middle_eq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex square 1 0 = toPerfectVerdierSequence.middleVertex
  right_eq : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex square 1 1 = toPerfectVerdierSequence.rightVertex
  bottom_edge : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ square ≫ perfectStableInfinityInclusion =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow verdier.inclusion).edge
  right_edge : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ square ≫ perfectStableInfinityInclusion =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow toPerfectVerdierSequence.projection).edge
  zero_corner : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (perfectStableObject (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex square 0 1))

end SerrePositivity.KST.SConstruction

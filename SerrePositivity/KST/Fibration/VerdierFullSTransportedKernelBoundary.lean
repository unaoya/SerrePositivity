module
public import SerrePositivity.KST.Fibration.VerdierFullSSquarePrismIso
public import SerrePositivity.KST.Fibration.QuotientSCoreSingleEdges

/-!
概要：全四角柱の始端四角形と元の商核四角形の、同じ包含・商の全一単体を照合する。
方針：全時刻固定した下側二胞体の二面を取り、元の厳密な境界比較へ接続する。
規約：全二胞体・共有対角・核円柱の比較を、境界二辺の等号だけで代用しない。
使われ方：K-6 c4 の元の商核と指定 Verdier 全四角形を結ぶ境界条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u})

/-- 同じ全四角柱の始端下辺は、元の商核の包含の全一単体そのもの。 -/
theorem verdierFullSTransportedSquare_bottom_kernel :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ verdierFullSTransportedSquare d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ quotientSKernelInfinitySquare d.inclusion d.projection := by
  have hb : stdSimplex.δ (2 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 1} 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  have h := congrArg (fun f => stdSimplex.δ (2 : Fin 3) ≫ f)
    (verdierFullSTransportedSquare_lower d)
  simp only [← Category.assoc, hb] at h
  exact h.trans (quotientSKernelInfinitySquare_bottom_eq_verdierSingle d).symm

/-- 同じ全四角柱の始端右辺は、元の商核の商の全一単体そのもの。 -/
theorem verdierFullSTransportedSquare_right_kernel :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ verdierFullSTransportedSquare d =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ quotientSKernelInfinitySquare d.inclusion d.projection := by
  have h := congrArg (fun f => stdSimplex.δ (0 : Fin 3) ≫ f)
    (verdierFullSTransportedSquare_lower d)
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge] at h
  exact h.trans (quotientSKernelInfinitySquare_right_eq_verdierSingle d).symm

/-- 元の包含辺を厳密に保持するので、全四角柱の始端左下は同じ商核頂点。 -/
theorem verdierFullSTransportedSquare_apex_kernel :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (verdierFullSTransportedSquare d) 0 0 =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (quotientSKernelInfinitySquare d.inclusion d.projection) 0 0 := by
  have h := congrArg (fun f : Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} =>
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}.δ 1 (SSet.yonedaEquiv f)) (verdierFullSTransportedSquare_bottom_kernel d)
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source _).symm.trans (h.trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source _))

end SerrePositivity.KST.Fibration

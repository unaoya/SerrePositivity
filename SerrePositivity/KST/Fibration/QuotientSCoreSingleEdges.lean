module
public import SerrePositivity.KST.Fibration.StableCoreSingleKanHom
public import SerrePositivity.KST.Fibration.QuotientSKernelEdges

/-! # 元の商核四角形の包含・商辺を、元の Verdier 四角形の一回の反復実現へ照合する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C)

/-- 元の商核四角形の商辺は、同じ商の一回の反復実現の全 ∞ 作用の辺である。 -/
theorem quotientSKernelInfinitySquare_right_multiSingle :
    squareRightEdge ≫ quotientSKernelInfinitySquare i q = SSet.yonedaEquiv.symm
      ((coherentNerveMap (stableMultiKanEnrichedFunctor 0)).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow q).edge) :=
  (quotientSKernelInfinitySquare_right i q).trans
    (congrArg SSet.yonedaEquiv.symm (stableMultiSingleKan_edge q).symm)

/-- 元の商核四角形の包含辺は、同じ包含の一回の反復実現の全 ∞ 作用の辺である。 -/
theorem quotientSKernelInfinitySquare_bottom_multiSingle :
    squareBottomEdge ≫ quotientSKernelInfinitySquare i q = SSet.yonedaEquiv.symm
      ((coherentNerveMap (stableMultiKanEnrichedFunctor 0)).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow i).edge) :=
  (quotientSKernelInfinitySquare_bottom i q).trans
    (congrArg SSet.yonedaEquiv.symm (stableMultiSingleKan_edge i).symm)

/-- 指定した元の Verdier 四角形の同じ商辺と、元の商核四角形の商辺は厳密に一致。 -/
theorem quotientSKernelInfinitySquare_right_eq_verdierSingle (d : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.{u}) :
    squareRightEdge ≫ quotientSKernelInfinitySquare d.inclusion d.projection =
      squareRightEdge ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)) := by
  rw [← Category.assoc, d.right_edge, SSet.yonedaEquiv_symm_comp]
  exact quotientSKernelInfinitySquare_right_multiSingle d.inclusion d.projection

/-- 指定した元の Verdier 四角形の同じ包含辺と、元の商核四角形の包含辺は厳密に一致。 -/
theorem quotientSKernelInfinitySquare_bottom_eq_verdierSingle (d : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.{u}) :
    squareBottomEdge ≫ quotientSKernelInfinitySquare d.inclusion d.projection =
      squareBottomEdge ≫ (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)) := by
  rw [← Category.assoc, d.bottom_edge, SSet.yonedaEquiv_symm_comp]
  exact quotientSKernelInfinitySquare_bottom_multiSingle d.inclusion d.projection

/-- 元の二四角形の同じ包含辺を保つので、元の左下頂点も厳密に一致する。 -/
theorem quotientSKernelInfinitySquare_apex_eq_verdierSingle (d : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.{u}) :
    squareVertex (quotientSKernelInfinitySquare d.inclusion d.projection) 0 0 =
      squareVertex (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)) 0 0 := by
  have he := congrArg (fun t : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} =>
    (SpaceInfinity.{u}).δ 1 (SSet.yonedaEquiv t))
      (quotientSKernelInfinitySquare_bottom_eq_verdierSingle d)
  exact (squareBottomEdge_source _).symm.trans (he.trans (squareBottomEdge_source _))

/-- 元の二四角形の同じ商辺を保つので、元の右下頂点も厳密に一致する。 -/
theorem quotientSKernelInfinitySquare_middle_eq_verdierSingle (d : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.{u}) :
    squareVertex (quotientSKernelInfinitySquare d.inclusion d.projection) 1 0 =
      squareVertex (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)) 1 0 := by
  have he := congrArg (fun t : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} =>
    (SpaceInfinity.{u}).δ 1 (SSet.yonedaEquiv t))
      (quotientSKernelInfinitySquare_right_eq_verdierSingle d)
  exact (squareRightEdge_source _).symm.trans (he.trans (squareRightEdge_source _))

/-- 元の二四角形の同じ商辺を保つので、元の右上頂点も厳密に一致する。 -/
theorem quotientSKernelInfinitySquare_target_eq_verdierSingle (d : _root_.SerrePositivity.InfinityCategories.Stable.Infinity.VerdierDiagram.{u}) :
    squareVertex (quotientSKernelInfinitySquare d.inclusion d.projection) 1 1 =
      squareVertex (d.square ≫ coherentNerveMap (stableMultiKanEnrichedFunctor 0)) 1 1 := by
  have he := congrArg (fun t : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u} =>
    (SpaceInfinity.{u}).δ 0 (SSet.yonedaEquiv t))
      (quotientSKernelInfinitySquare_right_eq_verdierSingle d)
  exact (squareRightEdge_target _).symm.trans (he.trans (squareRightEdge_target _))

end SerrePositivity.KST.Fibration

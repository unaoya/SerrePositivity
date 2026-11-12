module
public import SerrePositivity.KST.Fibration.VerdierLowerTriangleZeroHom
public import SerrePositivity.KST.Fibration.StableTriangleCompositeMap
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CommutativeSquareRealization

/-! # 指定 Verdier 下側二胞体の元の二短辺と、同じ包含・商の実合成 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 元の下側二胞体の第一短辺は、指定した元の包含の同じ一単体である。 -/
theorem verdierLowerTriangle_first_arrow (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 (verdierLowerTriangle d) = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.inclusion).edge := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 2 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ d.square)) = _
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableSquareTriangle_bottomEdge,
    d.bottom_edge, Equiv.apply_symm_apply]

/-- 元の下側二胞体の第二短辺は、指定した元の商の同じ一単体である。 -/
theorem verdierLowerTriangle_last_arrow (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 (verdierLowerTriangle d) = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableArrow d.projection).edge := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.δ 0 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ≫ d.square)) = _
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTriangle_rightEdge,
    d.right_edge, Equiv.apply_symm_apply]

/-- 元の下側二胞体の同じ合成 path は、指定した包含・商の元の実合成を回収する。 -/
theorem verdierLowerTriangleCompositeMap_heq (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    HEq (stableTriangleCompositeMap (verdierLowerTriangle d))
      (show d.left ⟶ d.right from (show d.left ⟶ d.middle from d.inclusion) ≫
        (show d.middle ⟶ d.right from d.projection)) :=
  stableTriangleCompositeMap_heq_of_faces _ d.inclusion d.projection
    (verdierLowerTriangle_first_arrow d) (verdierLowerTriangle_last_arrow d)

end SerrePositivity.KST.Fibration

module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PointHomBasePrism
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceModelEquivalence

/-!
概要：恒等点輸送で使う同じ全左 Hom の円柱は、区間写像空間への実際の同値を与える。
方針：円柱を既存の coslice fiber の区間比較の展開と厳密に同定する。
規約：cofinalPointJoinPrism による元の円柱自体を保持し、別の Hom 比較へ置き換えない。
使われ方：Tw の恒等点からの輸送のパラメーターを、Yoneda の実際の Hom 作用にそろえる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ全左 Hom の円柱を curry して、元の区間写像空間へ送る。 -/
def pointHomIntervalComparison {B : SSet.{u}} (a b : B _⦋0⦌) :
    pinchedHomLeft a b ⟶ intervalMappingSpace a b :=
  intervalMappingCurryOfEndpoints (HomotopyLimits.pointHomBasePrism a b)
    (HomotopyLimits.pointHomBasePrism_zero a b) (HomotopyLimits.pointHomBasePrism_one a b)

/-- その円柱の比較は、同じ coslice fiber に続く既存の区間比較そのもの。 -/
lemma pointHomIntervalComparison_eq {B : SSet.{u}} (a b : B _⦋0⦌) :
    pointHomIntervalComparison a b =
    (pinchedLeftCosliceFiberIso a b).hom ≫ cosliceFiberToIntervalMappingSpace a b := by
  apply intervalMappingUncurry_injective
  rw [pointHomIntervalComparison, intervalMappingUncurry_curryOfEndpoints,
    cosliceFiberToIntervalMappingSpace_uncurry]
  rfl

/-- 恒等点からの輸送の元の円柱による、全左 Hom の実際の区間比較は同値。 -/
lemma pointHomIntervalComparison_isQCatEquivalence {B : SSet.{u}} [Quasicategory B]
    (a b : B _⦋0⦌) : IsQCatEquivalence (pointHomIntervalComparison a b) := by
  rw [pointHomIntervalComparison_eq]
  exact (qCatEquivalenceOfIso (pinchedLeftCosliceFiberIso a b)).isQCatEquivalence.comp
    (cosliceFiberToIntervalMappingSpace_isQCatEquivalence a b)

end SerrePositivity.InfinityCategories

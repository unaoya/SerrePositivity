module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.Opposite
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentConeSectionSpace
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeSectionRestrictionCriterion
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationConeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.RepresentableCosliceComparison

/-!
概要：元の表現可能前層の小さい unstraightening の全錐上の切断制限。
方針：元の coslice の極限錐の切断判定を、同じ底上の復元比較で移す。
規約：形状の有限性も離散性も不要。元の全錐と底図式への制限を使う。
使われ方：元の Yoneda 前層の全有限余積保存の切断側の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- Cᵒᵖ の元の極限錐上で、同じ Yoneda 前層の全切断から底への制限は同値。 -/
lemma representableConeSectionRestriction_isQCatEquivalence
    {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C.op}
    (c : JoinCone D) (hc : IsLimitCone c) (y : C _⦋0⦌) :
    IsQCatEquivalence (leftFibrationConeRestriction
      (smallLeftUnstraighteningProjection (representablePresheafInfinity y)) c) := by
  apply (leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)))
    (smallLeftUnstraighteningProjection (representablePresheafInfinity y))
    (representableCosliceComparison y) (representableCosliceComparison_projection y)
    (representableCosliceComparison_isPrecompositionEquivalence y) c).mp
  exact ((isLimitCone_iff_coneSectionRestriction_homotopyEquivalence c).mp hc
    (SSet.opObjEquiv.symm y)).isQCatEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits

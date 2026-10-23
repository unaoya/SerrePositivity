module

public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentableUnstraighteningComparison
public import SerrePositivity.InfinityCategories.F1B.QuillenASliceOpposite

/-!
概要：元の反転 coslice から元の表現可能前層の小さい unstraightening への比較。
方針：元の slice 反転同型と元の Yoneda 前層の復元比較を底上で合成する。
規約：点の反転の正規化を保持し、新しい Hom 前層へ置き換えない。
使われ方：P_Σ への Yoneda 因子化の全錐の切断比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の反転した頂点の coslice から、同じ Yoneda 前層の全空間への比較。 -/
def representableCosliceComparison {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    sliceUnder (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)) ⟶
      smallLeftUnstraightening (representablePresheafInfinity y) :=
  (cofinalPointSliceOverOpIso y).inv.left ≫ representableLeftUnstraighteningComparison y

/-- 比較は元の反転した底 Cᵒᵖ を厳密に保持する。 -/
lemma representableCosliceComparison_projection
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    representableCosliceComparison y ≫
      smallLeftUnstraighteningProjection (representablePresheafInfinity y) =
        sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm y)) := by
  rw [representableCosliceComparison, Category.assoc,
    representableLeftUnstraighteningComparison_projection]
  exact (cofinalPointSliceOverOpIso y).inv.w

/-- 元の底上の比較は全空間の前合成同値。 -/
lemma representableCosliceComparison_isPrecompositionEquivalence
    {C : SSet.{u}} [Quasicategory C] (y : C _⦋0⦌) :
    IsPrecompositionEquivalence (representableCosliceComparison y) := by
  have hi : IsIso (cofinalPointSliceOverOpIso y).inv.left := by infer_instance
  exact (isPrecompositionEquivalence_of_iso (asIso (cofinalPointSliceOverOpIso y).inv.left)).comp
    (representableLeftUnstraighteningComparison_isPrecompositionEquivalence y)

end SerrePositivity.InfinityCategories.HomotopyLimits

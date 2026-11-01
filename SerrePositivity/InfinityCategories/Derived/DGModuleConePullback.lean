module
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberFiberComparisonProjection
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberPullback
public import SerrePositivity.InfinityCategories.Core.RightFibrationReflection

/-! # dg 加群の標準 cofiber 四角形の引き戻し性

概要：標準 cone 四角形は dg 加群 nerve の引き戻しでもある。
方針：実 slice 比較辺の可逆性を射影から反映し、標準 fiber の極限性を移す。
規約：安定性を前提にしない。使われ方：β3 の零角の双カルテジアン判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- cofiber から fiber への実際の slice 比較辺は可逆。 -/
lemma dgModuleCofiberFiberComparisonSliceEdge_isInvertible (f : M ⟶ N) :
    IsInvertibleEdge (X := sliceOver (pullbackCospan
      (dgModuleFiberSquare A D (moduleConeInr A D f))))
      (dgModuleCofiberFiberComparisonSliceEdge A D f) := by
  have he := dgModuleCofiberFiberLift_isInvertible A D f
  have hp := (isInvertibleEdge_congr (X := dgModuleNerve A D)
    (dgModuleCofiberFiberComparisonSliceEdge_projection A D f)).mpr he
  exact derived_rightFibration_reflects_invertibleEdge
    (sliceOverProjection (pullbackCospan (dgModuleFiberSquare A D (moduleConeInr A D f))))
    (dgModuleCofiberFiberComparisonSliceEdge A D f) hp

/-- 標準 dg 加群の cone 四角形は実際の ∞ 引き戻し四角形である。 -/
lemma dgModuleConeSquare_isPullback (f : M ⟶ N) :
    IsPullbackSquare (dgModuleConeSquare A D f) := by
  have := dgModuleCofiberFiberComparisonSliceEdge_isInvertible A D f
  have hc : IsLimitCone (dgModuleCofiberFiberSourceCone A D f) :=
    (dgModuleFiberCone_isLimit A D (moduleConeInr A D f)).of_vertexIso
      (asIso (SSet.Truncated.HomotopyCategory.homMk
        (dgModuleCofiberFiberComparisonSliceEdge A D f))).symm
  exact rebaseCone_isLimit (dgModuleCofiberFiberComparison_cospan A D f).symm
    (dgModuleCofiberFiberSourceCone A D f) hc

end SerrePositivity.InfinityCategories

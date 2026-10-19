module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberCofiberComparisonSlice
public import SerrePositivity.InfinityCategories.Derived.DGModuleTriangleAppendEdge
public import SerrePositivity.InfinityCategories.Derived.FiberCofiberComparisonProjection

/-! # 双対の coslice 比較辺の射影

概要：coslice の比較辺の射影は明示的な cofiber 比較鎖写像の辺と一致する。
方針：join の右因子を左セルの最後の二頂点で計算する。
規約：端点の表記の違いを許して一単体を同定する。使われ方：β3 の比較辺の可逆性。
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

/-- 比較 join 写像の右因子への制限は明示的比較射の辺。 -/
lemma dgModuleFiberCofiberComparisonJoin_suffix (f : M ⟶ N) :
    joinInr (SSet.horn 2 0 : SSet.{max (u + 1) v}) Δ[1] ≫ dgModuleFiberCofiberComparisonJoin A D f =
      SSet.yonedaEquiv.symm (dgModuleEdge A D (dgModuleFiberCofiberDesc A D f)).edge := by
  rw [← spanJoinLeft_lastEdge, Category.assoc, dgModuleFiberCofiberComparisonJoin_left,
    SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  exact dgModuleTriangleAppend_lastEdge A D _ _ _ _ _ _

/-- Coslice 比較辺の射影は明示的比較射と同じ一単体。 -/
lemma dgModuleFiberCofiberComparisonSliceEdge_projection (f : M ⟶ N) :
    ((dgModuleFiberCofiberComparisonSliceEdge A D f).map ((SSet.truncation 2).map
      (sliceUnderProjection (pushoutSpan
        (dgModuleConeSquare A D (dgModuleFiberProjection A D f)))))).edge =
      (dgModuleEdge A D (dgModuleFiberCofiberDesc A D f)).edge := by
  change (sliceUnderProjection (pushoutSpan
        (dgModuleConeSquare A D (dgModuleFiberProjection A D f)))).app _
    (SSet.yonedaEquiv (sliceUnderCurry (dgModuleFiberCofiberComparisonJoin A D f)
      (dgModuleFiberCofiberComparisonJoin_fixed A D f))) = _
  rw [← SSet.yonedaEquiv_comp, sliceUnderCurry_projection,
    dgModuleFiberCofiberComparisonJoin_suffix]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.InfinityCategories

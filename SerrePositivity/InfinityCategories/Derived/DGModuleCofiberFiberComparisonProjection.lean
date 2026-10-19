module
public import SerrePositivity.InfinityCategories.Derived.DGModuleCofiberFiberComparisonSlice
public import SerrePositivity.InfinityCategories.Derived.CofiberFiberComparisonProjection
public import SerrePositivity.InfinityCategories.Core.RightFibration

/-! # 錐比較辺の射影は明示的な比較写像

概要：slice の実際の比較辺を射影した一単体を dgModuleCofiberFiberLift の辺と同定する。
方針：join の先頭を左セルの先頭二頂点で計算し、比較単体の最初の辺を読む。
規約：端点の等式だけに依存する。使われ方：β3 の比較辺の可逆性。
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

/-- 比較 join 写像の左因子への制限は明示的な比較射の辺。 -/
lemma dgModuleCofiberFiberComparisonJoin_prefix (f : M ⟶ N) :
    joinInl (Δ[1] : SSet) (SSet.horn 2 2) ≫ dgModuleCofiberFiberComparisonJoin A D f =
      SSet.yonedaEquiv.symm (dgModuleEdge A D (dgModuleCofiberFiberLift A D f)).edge := by
  rw [← cospanJoinLeft_firstEdge, Category.assoc, dgModuleCofiberFiberComparisonJoin_left,
    SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  refine (prepend_triangle_firstEdge _ _).trans ?_
  exact congrArg (fun c => Simplex.ofEdge
    (HomotopyComparison.pairObj (ForgetEnrichment.to (Complex A) M)
      (dgModuleFiber A D (moduleConeInr A D f))) c)
    (dgModuleCofiberFiberComparisonCycle_eq A D f)

/-- 実際の slice 比較辺を射影すると明示的比較射と同じ一単体になる。 -/
lemma dgModuleCofiberFiberComparisonSliceEdge_projection (f : M ⟶ N) :
    ((dgModuleCofiberFiberComparisonSliceEdge A D f).map ((SSet.truncation 2).map
      (sliceOverProjection (pullbackCospan (dgModuleFiberSquare A D (moduleConeInr A D
        f)))))).edge =
      (dgModuleEdge A D (dgModuleCofiberFiberLift A D f)).edge := by
  change (sliceOverProjection (pullbackCospan (dgModuleFiberSquare A D (moduleConeInr A D
    f)))).app _
    (SSet.yonedaEquiv (sliceOverCurry (dgModuleCofiberFiberComparisonJoin A D f)
      (dgModuleCofiberFiberComparisonJoin_fixed A D f))) = _
  rw [← SSet.yonedaEquiv_comp, sliceOverCurry_projection, dgModuleCofiberFiberComparisonJoin_prefix]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.InfinityCategories

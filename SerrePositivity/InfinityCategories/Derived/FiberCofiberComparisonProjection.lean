module
public import SerrePositivity.InfinityCategories.Derived.FiberCofiberComparisonSlice
public import SerrePositivity.InfinityCategories.Derived.TriangleAppendEdge
public import SerrePositivity.InfinityCategories.Core.RightFibration

/-! # 双対の coslice 比較辺の射影

概要：coslice の比較辺の射影は明示的な cofiber 比較鎖写像の辺と一致する。
方針：join の右因子を左セルの最後の二頂点で計算する。
規約：端点の表記の違いを許して一単体を同定する。使われ方：D7 の比較辺の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial

/-- 左セルの最後の辺は span の join の右因子。 -/
lemma spanJoinLeft_lastEdge :
    SSet.stdSimplex.map (SimplexCategory.mkHom (joinRightOrderHom 1 1)) ≫
      spanJoinLeft.{u} 1 = joinInr (SSet.horn 2 0 : SSet.{u}) Δ[1] := by
  unfold spanJoinLeft
  change SSet.stdSimplex.map (SimplexCategory.mkHom
    (cofiberJoinRightOrderHom 1 1 3 (by omega))) ≫ _ = _
  rw [← cofiberJoinStdSimplexIso_inr]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, joinInr_joinMap, Category.id_comp]

variable {S : Type u} [CommRing S] {B C D : Complex S}

/-- 比較 join 写像の右因子への制限は明示的比較射の辺。 -/
lemma fiberCofiberComparisonJoin_suffix (g : B ⟶ D) (h : C ⟶ D) :
    joinInr (SSet.horn 2 0 : SSet.{u + 1}) Δ[1] ≫ fiberCofiberComparisonJoin g h =
      SSet.yonedaEquiv.symm (complexEdge (fiberCofiberDesc g h)).edge := by
  rw [← spanJoinLeft_lastEdge, Category.assoc, fiberCofiberComparisonJoin_left,
    SSet.yonedaEquiv_symm_naturality_left]
  apply congrArg SSet.yonedaEquiv.symm
  exact complexTriangleAppend_lastEdge _ _ _ _ _ _

/-- Coslice 比較辺の射影は明示的比較射と同じ一単体。 -/
lemma fiberCofiberComparisonSliceEdge_projection (g : B ⟶ D) (h : C ⟶ D) :
    ((fiberCofiberComparisonSliceEdge g h).map ((SSet.truncation 2).map
      (sliceUnderProjection (pushoutSpan (standardCofiberSquare
        (pullbackProjectionB g h) (pullbackProjectionC g h)))))).edge =
      (complexEdge (fiberCofiberDesc g h)).edge := by
  change (sliceUnderProjection (pushoutSpan (standardCofiberSquare
    (pullbackProjectionB g h) (pullbackProjectionC g h)))).app _
    (SSet.yonedaEquiv (sliceUnderCurry (fiberCofiberComparisonJoin g h)
      (fiberCofiberComparisonJoin_fixed g h))) = _
  rw [← SSet.yonedaEquiv_comp, sliceUnderCurry_projection, fiberCofiberComparisonJoin_suffix]
  exact SSet.yonedaEquiv.apply_symm_apply _

end SerrePositivity.InfinityCategories

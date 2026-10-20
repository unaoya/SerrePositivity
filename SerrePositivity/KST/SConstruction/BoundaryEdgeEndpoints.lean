module
public import SerrePositivity.KST.SConstruction.FixedCylinderAttachment

/-! # 全区間境界の厳密な一致から同じ両端を回収する
概要：元の全区間境界の等号を、元の二つの端点面の厳密な等号へ移す。
方針：標準端点面を区間境界への包含と同じ境界包含に分解する。
規約：写像先での成分ではなく、元の全零単体写像の等号を回収する。
使われ方：全境界固定円柱の出口と元の隣接辺を同じホーンに貼る。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 元の全区間境界が等しければ、両端面の全写像も厳密に等しい。 -/
lemma boundaryEdgeEndpoint {E : SSet.{u}} (a b : (Δ[1] : SSet.{u}) ⟶ E)
    (h : (SSet.boundary 1).ι ≫ a = (SSet.boundary 1).ι ≫ b) (i : Fin 2) :
    stdSimplex.δ i ≫ a = stdSimplex.δ i ≫ b := by
  rw [← SSet.boundary.ι_ι i, Category.assoc, h, ← Category.assoc, SSet.boundary.ι_ι]

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.InnerVariableOuterMap
public import Mathlib.Logic.Equiv.Fin.Rotate

/-! # 最内側の可変座標と巡回置換
概要：最後に置く可変次数の元の添字を、先頭を最後へ移す有限置換と照合する。
方針：最後の座標と castSucc の座標で対象と射を比較する。
規約：元の innerVariableIndex を保つ。使われ方：全多単体的な座標比較と全零境界の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 外側の次数変更は最後の可変座標では恒等射。 -/
lemma innerVariableOuterMap_last (r : ℕ) {d e : Fin r → SimplexCategoryᵒᵖ}
    (f : d ⟶ e) (k : SimplexCategoryᵒᵖ) :
    eqToHom (innerVariableIndex_obj_last r d k).symm ≫
      innerVariableOuterMap r f k (Fin.last r) ≫
        eqToHom (innerVariableIndex_obj_last r e k) = 𝟙 k := by
  induction r with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _)
  | succ r ih => exact ih (fun i => f i.succ)

/-- 外側の次数変更は最後以外の各座標で元の作用素を回収する。 -/
lemma innerVariableOuterMap_castSucc (r : ℕ) {d e : Fin r → SimplexCategoryᵒᵖ}
    (f : d ⟶ e) (k : SimplexCategoryᵒᵖ) (i : Fin r) :
    eqToHom (innerVariableIndex_obj_castSucc r d k i).symm ≫
      innerVariableOuterMap r f k i.castSucc ≫
        eqToHom (innerVariableIndex_obj_castSucc r e k i) = f i := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    cases i using Fin.cases with
    | zero => exact (Category.id_comp _).trans (Category.comp_id _)
    | succ i => exact ih (fun j => f j.succ) i

/-- 巡回置換は最後以外の座標を一つ先へ送る。 -/
lemma finRotate_castSucc (r : ℕ) (i : Fin r) :
    finRotate (r + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt

/-- 元の最内側の可変添字は、全添字の先頭を最後へ移す巡回置換。 -/
lemma innerVariableIndex_obj_permutation (r : ℕ) (d : Fin (r + 1) → SimplexCategoryᵒᵖ) :
    (innerVariableIndex r (fun i => d i.succ)).obj (d 0) =
      (Pi.comap (fun _ : Fin (r + 1) => SimplexCategoryᵒᵖ) (finRotate (r + 1))).obj d := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Pi.comap_obj, finRotate_last] using
      innerVariableIndex_obj_last r (fun i => d i.succ) (d 0)
  · simpa only [Pi.comap_obj, finRotate_castSucc] using
      innerVariableIndex_obj_castSucc r (fun i => d i.succ) (d 0) j

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.ArCutEvaluation

/-! # 切断の左右の短い区間と端点の収縮
概要：左右の短い標準区間を元の区間へ埋め込み、元の区間を各側へ収縮する。
方針：左は min、右は切り捨て差と平行移動を使う。
規約：切断が両端の場合も含む。使われ方：支持部分圏と S_k・S_(n-k) の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 左側の短い区間の元の区間への包含。 -/
def cutLeftIntervalInclusion (n : ℕ) (k : Fin (n + 1)) :
    Fin (k.val + 1) →o Fin (n + 1) where
  toFun i := ⟨i.val, by have := i.isLt; have := k.isLt; omega⟩
  monotone' _i _j h := h

/-- 元の区間を左側の短い区間へ min で収縮する。 -/
def cutLeftIntervalRetraction (n : ℕ) (k : Fin (n + 1)) :
    Fin (n + 1) →o Fin (k.val + 1) where
  toFun i := ⟨min i.val k.val, Nat.lt_succ_of_le (min_le_right _ _)⟩
  monotone' _i _j h := min_le_min h le_rfl

/-- 右側の短い区間の元の区間への包含。 -/
def cutRightIntervalInclusion (n : ℕ) (k : Fin (n + 1)) :
    Fin (n - k.val + 1) →o Fin (n + 1) where
  toFun i := ⟨i.val + k.val, by have := i.isLt; have := k.isLt; omega⟩
  monotone' _i _j h := Nat.add_le_add_right h _

/-- 元の区間を右側の短い区間へ切り捨て差で収縮する。 -/
def cutRightIntervalRetraction (n : ℕ) (k : Fin (n + 1)) :
    Fin (n + 1) →o Fin (n - k.val + 1) where
  toFun i := ⟨i.val - k.val, by have := i.isLt; have := k.isLt; omega⟩
  monotone' _i _j h := Nat.sub_le_sub_right h _

/-- 左側の包含の後の収縮は短い区間の恒等写像。 -/
lemma cutLeftInterval_retraction_inclusion (n : ℕ) (k : Fin (n + 1)) :
    (cutLeftIntervalRetraction n k).comp (cutLeftIntervalInclusion n k) = OrderHom.id := by
  apply DFunLike.ext
  intro i
  apply Fin.ext
  change min i.val k.val = i.val
  exact min_eq_left (Nat.le_of_lt_succ i.isLt)

/-- 左側への収縮の後の包含は min による切断そのもの。 -/
lemma cutLeftInterval_inclusion_retraction (n : ℕ) (k : Fin (n + 1)) :
    (cutLeftIntervalInclusion n k).comp (cutLeftIntervalRetraction n k) =
      cutCornerOrder k 0 0 := by
  apply DFunLike.ext
  intro i
  exact (congrArg Fin.val (cutEndpoint_zero_zero k i)).symm |> Fin.ext

/-- 右側の包含の後の収縮は短い区間の恒等写像。 -/
lemma cutRightInterval_retraction_inclusion (n : ℕ) (k : Fin (n + 1)) :
    (cutRightIntervalRetraction n k).comp (cutRightIntervalInclusion n k) = OrderHom.id := by
  apply DFunLike.ext
  intro i
  apply Fin.ext
  exact Nat.add_sub_cancel i.val k.val

/-- 右側への収縮の後の包含は max による切断そのもの。 -/
lemma cutRightInterval_inclusion_retraction (n : ℕ) (k : Fin (n + 1)) :
    (cutRightIntervalInclusion n k).comp (cutRightIntervalRetraction n k) =
      cutCornerOrder k 1 1 := by
  apply DFunLike.ext
  intro i
  apply Fin.ext
  change i.val - k.val + k.val = (cutEndpoint k i 1 1).val
  rw [cutEndpoint_one_one]
  change i.val - k.val + k.val = max i.val k.val
  omega

end SerrePositivity.KST.SConstruction

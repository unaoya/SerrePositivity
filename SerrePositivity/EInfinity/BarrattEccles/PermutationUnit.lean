module

public import SerrePositivity.EInfinity.BarrattEccles.PermutationComposition

/-!
# 置換の部分合成の単位則

概要：Berger–Fresse §0.10 の置換の部分合成が一入力の恒等置換を単位に持つことを示す。
方針：一入力の挿入分解と空の外側の残りの入力を直接計算する。
規約：左単位則の出力 arity 0+n は Fin.cast によって n と同定する。
使われ方：Barratt–Eccles の shuffle 部分合成の単位則を頂点ごとに証明する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：一入力の挿入分解の残りの入力は位置を変えない（Berger–Fresse §0.10）。
方針：挿入分解の逆写像の二つの場合を計算し、加減算を相殺する。
規約：挿入する arity は 1 である。
使われ方：外側置換が一入力の挿入によって変わらないことを示す。 -/
lemma insertionEquiv_one_symm_left (m : ℕ) (i : Fin (m + 1))
    (j : {j : Fin (m + 1) // j ≠ i}) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m 1 i).symm (Sum.inl j) = j.val := by
  apply Fin.ext
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv, Equiv.coe_fn_symm_mk]
  split_ifs <;> rfl

/-- 概要：一入力の挿入の外側置換は元の置換である（Berger–Fresse §0.10）。
方針：挿入分解の残りの入力と唯一の内側入力に分けて作用を比較する。
規約：挿入位置 i は任意である。
使われ方：置換の部分合成の右単位則となる。 -/
lemma outerPermutation_arity_one (m : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m 1 i σ = σ := by
  apply Equiv.ext
  intro x
  obtain ⟨j, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m 1 i).symm.surjective x
  cases j with
  | inl j =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_remaining, insertionEquiv_one_symm_left,
      insertionEquiv_one_symm_left]
    rfl
  | inr j =>
    have hj : j = 0 := Fin.eq_zero j
    subst j
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation_inside m 1 i σ 0

/-- 概要：一入力の恒等置換を代入しても外側の置換は変わらない（Berger–Fresse §0.10）。
方針：内側の単位置換の延長を消し、一入力の外側置換の公式を使う。
規約：出力 arity は m+1 である。
使われ方：shuffle の右単位則を各頂点で証明する。 -/
@[simp] lemma permutationComposition_right_unit (m : ℕ) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) : permutationComposition m 1 i σ 1 = σ := by
  rw [permutationComposition, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_one, mul_one, outerPermutation_arity_one]

/-- 概要：一入力の外側の恒等置換への代入は内側の置換である（Berger–Fresse §0.10）。
方針：全入力が挿入区間に属することから内側置換の区間内の公式を適用する。
規約：出力 Fin(0+n) を Fin n へ次数移送して比較する。
使われ方：shuffle の左単位則を各頂点で証明する。 -/
lemma permutationComposition_left_unit (n : ℕ) (τ : Equiv.Perm (Fin n)) (x : Fin (0 + n)) :
    Fin.cast (Nat.zero_add n) (permutationComposition 0 n 0 1 τ x) =
      τ (Fin.cast (Nat.zero_add n) x) := by
  let j := Fin.cast (Nat.zero_add n) x
  have hx : x = (⟨(0 : Fin 1).val + j.val, by have h := j.isLt; omega⟩ : Fin (0 + n)) := by
    apply Fin.ext
    simp only [Fin.val_zero, Nat.zero_add]
    rfl
  rw [permutationComposition, outerPermutation_one, one_mul, hx, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation_inside]
  have hj : Fin.cast (Nat.zero_add n)
      (⟨(0 : Fin 1).val + j.val, by have h := j.isLt; omega⟩ : Fin (0 + n)) = j := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_zero, Nat.zero_add]
  rw [hj]
  apply Fin.ext
  simp only [Fin.val_cast, Fin.val_zero, Nat.zero_add]

end SerrePositivity.EInfinity.BarrattEccles

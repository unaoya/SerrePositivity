module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEnumerationRank
public import SerrePositivity.EInfinity.BarrattEccles.PermutationDeletionBlocks
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleVerticalFace

/-!
# 垂直辺を削除した shuffle の符号

概要：Berger–Fresse §1.1.3 の垂直辺の削除と shuffle 置換の削除を同定する。
方針：削除後の二ブロックの単調性と水平辺の所属を検査して、signature の削除公式を適用する。
規約：第二ブロックの入力位置には水平次数 p のずれがある。
使われ方：Leibniz 則の第二の項の Koszul 符号を得る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：垂直辺を削除した置換は小さい shuffle の置換に一致する（Berger–Fresse §1.1.3）。
方針：二ブロックの単調性を保存し、水平辺の所属を削除の可換図式で判定する。
規約：削除する入力は元の shuffle 置換で辺 a に送られる位置。
使われ方：一般の置換の削除の signature の公式を shuffle に適用する。 -/
lemma verticalDeletion_permutation {p q : ℕ} (s : ShufflePath p (q + 1))
    (a : Fin (p + (q + 1))) (ha : a ∉ s.val) :
    deletePermutation s.permutation (s.permutation.symm a) =
      ((verticalInsertionEquiv p q a).symm ⟨s, ha⟩).permutation := by
  let j := s.permutation.symm a
  have hja : s.permutation j = a := s.permutation.apply_symm_apply a
  have hj : p ≤ j.val := by
    apply le_of_not_gt
    intro h
    have hm := (s.permutation_mem_iff j).2 h
    rw [hja] at hm
    exact ha hm
  have hboundary := fun x : Fin (p + q) => succAbove_lt_boundary_of_ge j hj x
  have hmono := deletePermutation_preserves_blocks (P := p) (Q := p) s.permutation j hboundary
    s.permutation_strictMonoOn_left s.permutation_strictMonoOn_right
  apply ShufflePath.permutation_eq_of_blocks _ _ hmono.1 hmono.2
  intro x
  change deletePermutation s.permutation j x ∈ erasePosition s.val a ↔ x.val < p
  rw [mem_erasePosition]
  have hd := deletePermutation_succAbove s.permutation j x
  erw [hja] at hd
  erw [hd, s.permutation_mem_iff]
  exact hboundary x

/-- 概要：垂直辺を削除した shuffle の signature の比較（Berger–Fresse §1.1.3）。
方針：一般の置換の削除の公式に、逆像の位置の垂直座標による記述を代入する。
規約：a の直前の垂直座標と水平次数 p を含む符号。
使われ方：境界面の符号と掛けて第二の入力の微分の符号に直す。 -/
lemma sign_verticalDeletion {p q : ℕ} (s : ShufflePath p (q + 1))
    (a : Fin (p + (q + 1))) (ha : a ∉ s.val) :
    s.sign = (-1 : ℤˣ) ^ (a.val + (p + (s.vertical a.castSucc).val)) *
      ((verticalInsertionEquiv p q a).symm ⟨s, ha⟩).sign := by
  have h := sign_deletePermutation s.permutation (s.permutation.symm a)
  erw [s.permutation.apply_symm_apply, verticalDeletion_permutation s a ha,
    s.permutation_symm_val_of_notMem a ha] at h
  exact h

/-- 概要：垂直面の境界符号は小さい shuffle の符号と Koszul 符号に一致する（Berger–Fresse §1.1.3）。
方針：辺 a の後の頂点の境界符号を掛け、同じ位置番号が二度現れる偶数の冪を消す。
規約：第二の入力の微分には (−1)^p が付く。
使われ方：垂直な同方向の面と終端面の符号を Leibniz 則へ接続する。 -/
lemma verticalBoundary_sign {p q : ℕ} (s : ShufflePath p (q + 1))
    (a : Fin (p + (q + 1))) (ha : a ∉ s.val) :
    (-1 : ℤˣ) ^ (a.val + 1) * s.sign =
      (-1 : ℤˣ) ^ p * (-1 : ℤˣ) ^ (s.vertical a.succ).val *
        ((verticalInsertionEquiv p q a).symm ⟨s, ha⟩).sign := by
  have hv := (s.step_of_notMem a ha).2
  rw [sign_verticalDeletion s a ha, hv, ← mul_assoc, ← pow_add]
  have he : (a.val + 1) + (a.val + (p + (s.vertical a.castSucc).val)) =
      2 * a.val + (p + ((s.vertical a.castSucc).val + 1)) := by omega
  rw [he, pow_add, pow_mul]
  have hsq : (-1 : ℤˣ) ^ 2 = 1 := by decide
  rw [hsq, one_pow, one_mul, pow_add]

end SerrePositivity.EInfinity.BarrattEccles

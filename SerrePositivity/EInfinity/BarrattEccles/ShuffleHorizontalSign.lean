module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEnumerationRank
public import SerrePositivity.EInfinity.BarrattEccles.PermutationDeletionBlocks
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleHorizontalFace

/-!
# 水平辺を削除した shuffle の符号

概要：Berger–Fresse §1.1.3 の水平辺の削除と置換の削除の signature を比較する。
方針：辺数の括弧を移して一般の削除公式を適用し、小さい shuffle の置換を特徴づける。
規約：水平辺の削除では第一ブロックの大きさが p+1 から p となる。
使われ方：shuffle の Leibniz 則の第一の入力の微分の符号を計算する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：水平辺の削除に使う次数へ shuffle 置換を移す（Berger–Fresse §1.1.3）。
方針：辺数 (p+1)+q と (p+q)+1 の同値によって置換を共役する。
規約：頂点番号の自然数としての値は変えない。
使われ方：一般の Fin (N+1) の置換の削除を水平辺に適用する。 -/
def ShufflePath.horizontalTransportPermutation {p q : ℕ} (s : ShufflePath (p + 1) q) :
    Equiv.Perm (Fin (p + q + 1)) :=
  (finCongr (by omega : p + 1 + q = p + q + 1)).permCongr s.permutation

/-- 概要：次数を移しても水平辺の削除後の置換は小さい shuffle の置換である（Berger–Fresse §1.1.3）。
方針：削除後の二ブロックの単調性と水平辺集合への対応から置換の一意性を使う。
規約：削除する入力位置も辺数の同値によって移す。
使われ方：置換の削除による signature の公式を水平辺へ適用する。 -/
lemma horizontalDeletion_permutation {p q : ℕ} (s : ShufflePath (p + 1) q)
    (a : Fin (p + 1 + q)) (ha : a ∈ s.val) :
    deletePermutation s.horizontalTransportPermutation
        (Fin.cast (by omega) (s.permutation.symm a)) =
      ((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩).permutation := by
  let e : Fin (p + 1 + q) ≃ Fin (p + q + 1) := finCongr (by omega)
  let σ := s.horizontalTransportPermutation
  let S := s.val.map e.toEmbedding
  let j := e (s.permutation.symm a)
  have hja : σ j = e a := by
    change e (s.permutation (e.symm (e (s.permutation.symm a)))) = e a
    rw [e.symm_apply_apply, s.permutation.apply_symm_apply]
  have hj : j.val ≤ p := by
    have h := (s.permutation_mem_iff (s.permutation.symm a)).1
      (by simpa only [s.permutation.apply_symm_apply] using ha)
    change (s.permutation.symm a).val ≤ p
    omega
  have hboundary := fun x : Fin (p + q) => succAbove_lt_boundary_of_le j hj x
  have hleft : StrictMonoOn σ {x | x.val < p + 1} := by
    intro x hx y hy hxy
    change (s.permutation (e.symm x)).val < (s.permutation (e.symm y)).val
    exact s.permutation_strictMonoOn_left hx hy hxy
  have hright : StrictMonoOn σ {x | p + 1 ≤ x.val} := by
    intro x hx y hy hxy
    change (s.permutation (e.symm x)).val < (s.permutation (e.symm y)).val
    exact s.permutation_strictMonoOn_right hx hy hxy
  have hmem : ∀ x, σ x ∈ S ↔ x.val < p + 1 := by
    intro x
    change e (s.permutation (e.symm x)) ∈ s.val.map e.toEmbedding ↔ x.val < p + 1
    rw [Finset.mem_map_equiv, e.symm_apply_apply]
    exact s.permutation_mem_iff (e.symm x)
  have hmono := deletePermutation_preserves_blocks (P := p + 1) (Q := p)
    σ j hboundary hleft hright
  apply ShufflePath.permutation_eq_of_blocks _ _ hmono.1 hmono.2
  intro x
  change deletePermutation σ j x ∈ erasePosition S (e a) ↔ x.val < p
  rw [mem_erasePosition]
  have hd := deletePermutation_succAbove σ j x
  rw [hja] at hd
  rw [hd, hmem]
  exact hboundary x

/-- 概要：水平辺を削除した shuffle の signature の比較（Berger–Fresse §1.1.3）。
方針：次数の同値が signature を保つことと、水平辺の逆像位置の公式を使う。
規約：指数は辺の位置と直前の水平座標の和である。
使われ方：境界の符号と掛けて第一の入力の面の符号に直す。 -/
lemma sign_horizontalDeletion {p q : ℕ} (s : ShufflePath (p + 1) q)
    (a : Fin (p + 1 + q)) (ha : a ∈ s.val) :
    s.sign = (-1 : ℤˣ) ^ (a.val + (s.horizontal a.castSucc).val) *
      ((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩).sign := by
  have h := sign_deletePermutation s.horizontalTransportPermutation
    (Fin.cast (by omega) (s.permutation.symm a))
  rw [horizontalDeletion_permutation s a ha] at h
  have hsign : Equiv.Perm.sign s.horizontalTransportPermutation = s.sign :=
    Equiv.Perm.sign_permCongr _ _
  rw [hsign] at h
  have hval :
      (s.horizontalTransportPermutation (Fin.cast (by omega) (s.permutation.symm a))).val =
        a.val := by
    change (s.permutation (s.permutation.symm a)).val = a.val
    rw [s.permutation.apply_symm_apply]
  rw [hval] at h
  simpa only [Fin.val_cast, s.permutation_symm_val_of_mem a ha, ShufflePath.sign] using h

/-- 概要：水平面の境界符号は第一の入力の面の符号と小さい shuffle の符号に一致する（Berger–Fresse §1.1.3）。
方針：削除の符号に境界符号を掛け、辺位置の偶数倍を指数から消す。
規約：第一の入力の微分には追加の Koszul 符号はない。
使われ方：水平な同方向の面と終端面を Leibniz 則へ接続する。 -/
lemma horizontalBoundary_sign {p q : ℕ} (s : ShufflePath (p + 1) q)
    (a : Fin (p + 1 + q)) (ha : a ∈ s.val) :
    (-1 : ℤˣ) ^ (a.val + 1) * s.sign =
      (-1 : ℤˣ) ^ (s.horizontal a.succ).val *
        ((horizontalInsertionEquiv p q a).symm ⟨s, ha⟩).sign := by
  have hh := (s.step_of_mem a ha).1
  rw [sign_horizontalDeletion s a ha, hh, ← mul_assoc, ← pow_add]
  have he : (a.val + 1) + (a.val + (s.horizontal a.castSucc).val) =
      2 * a.val + ((s.horizontal a.castSucc).val + 1) := by omega
  rw [he, pow_add, pow_mul]
  have hsq : (-1 : ℤˣ) ^ 2 = 1 := by decide
  rw [hsq, one_pow, one_mul]

end SerrePositivity.EInfinity.BarrattEccles

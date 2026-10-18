module

public import SerrePositivity.EInfinity.BarrattEccles.PermutationInsertion

/-!
# 置換の削除と二ブロックの順序

概要：Berger–Fresse §1.1.3 の shuffle 置換の削除が二つのブロックの昇順性を保つことを示す。
方針：入力と出力の削除の可換図式を、欠落点を飛ばす写像の狭義単調性で検査する。
規約：入力ブロックの境目は自然数で指定する。
使われ方：削除後の置換を小さい shuffle 置換の特徴づけへ適用する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：第二ブロックの位置を飛ばしても第一ブロックの境目は変わらない（Berger–Fresse §1.1.3）。
方針：succAbove の前後の二つの場合を位置番号の不等式に直す。
規約：飛ばす位置 j は境目 P 以上である。
使われ方：垂直辺を削除した shuffle の入力ブロックを判定する。 -/
lemma succAbove_lt_boundary_of_ge {N P : ℕ} (j : Fin (N + 1)) (hj : P ≤ j.val)
    (x : Fin N) : (j.succAbove x).val < P ↔ x.val < P := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ]
  all_goals omega

/-- 概要：第一ブロックの位置を飛ばすと境目は一つ小さくなる（Berger–Fresse §1.1.3）。
方針：入力位置が飛ばす位置の前か後かで場合分けする。
規約：大きい境目は P+1、飛ばす位置 j は P 以下である。
使われ方：水平辺を削除した shuffle の入力ブロックを判定する。 -/
lemma succAbove_lt_boundary_of_le {N P : ℕ} (j : Fin (N + 1)) (hj : j.val ≤ P)
    (x : Fin N) : (j.succAbove x).val < P + 1 ↔ x.val < P := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp only [Fin.val_castSucc, Fin.val_succ]
  all_goals omega

/-- 概要：一点の削除は対応する二ブロックの昇順性を保つ（Berger–Fresse §1.1.3）。
方針：削除後の出力へ succAbove を適用し、元の置換のブロック上の単調性を使う。
規約：P は削除前の境目、Q は削除後の境目で、入力側の対応を hboundary で指定する。
使われ方：水平辺と垂直辺のどちらの削除でも小さい shuffle の昇順性を導く。 -/
lemma deletePermutation_preserves_blocks {N P Q : ℕ} (σ : Equiv.Perm (Fin (N + 1)))
    (j : Fin (N + 1)) (hboundary : ∀ x : Fin N, (j.succAbove x).val < P ↔ x.val < Q)
    (hleft : StrictMonoOn σ {x | x.val < P})
    (hright : StrictMonoOn σ {x | P ≤ x.val}) :
    StrictMonoOn (deletePermutation σ j) {x | x.val < Q} ∧
      StrictMonoOn (deletePermutation σ j) {x | Q ≤ x.val} := by
  constructor
  · intro x hx y hy hxy
    apply (Fin.strictMono_succAbove (σ j)).lt_iff_lt.mp
    rw [deletePermutation_succAbove, deletePermutation_succAbove]
    exact hleft ((hboundary x).2 hx) ((hboundary y).2 hy) ((Fin.strictMono_succAbove j) hxy)
  · intro x hx y hy hxy
    have hx' : P ≤ (j.succAbove x).val :=
      le_of_not_gt (fun h => (not_lt_of_ge hx) ((hboundary x).1 h))
    have hy' : P ≤ (j.succAbove y).val :=
      le_of_not_gt (fun h => (not_lt_of_ge hy) ((hboundary y).1 h))
    apply (Fin.strictMono_succAbove (σ j)).lt_iff_lt.mp
    rw [deletePermutation_succAbove, deletePermutation_succAbove]
    exact hright hx' hy' ((Fin.strictMono_succAbove j) hxy)

end SerrePositivity.EInfinity.BarrattEccles

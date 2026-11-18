module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapSingle
public import Mathlib.Tactic.FinCases

/-!
模型。文献の定義との比較は後で
# 一つの共有位置で決まる二部分割

概要：Berger–Fresse §1.2.4 の二つの重なる部分語を、内側語の一つの有限位置で表す。
方針：部分長を q+1 と l−q とし、総長条件から逆に共有位置を取り出す。
規約：内側語長は正。両部分語は非空で共有位置を一回ずつ含む。
使われ方：非零な外側辺切断の二出現色への内側作用と合成項の対応。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition

/-- 概要：共有位置 q で指定される二部分割（BF §1.2.4）。
方針：先頭部分を q+1 文字、後続部分を l−q 文字にする。
規約：共有する文字は両方に含める。
使われ方：内側の辺切断点から合成の分割を作る。 -/
def two {l : ℕ} (q : Fin l) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition 2 l := by
  refine ⟨![⟨q.val + 1, by omega⟩, ⟨l - q.val, by omega⟩], ?_, ?_⟩
  · intro i
    fin_cases i
    · change 0 < q.val + 1 ∨ l = 0
      omega
    · change 0 < l - q.val ∨ l = 0
      omega
  · change (∑ i : Fin 2, (![q.val + 1, l - q.val] : Fin 2 → ℕ) i) + 1 = l + 2
    rw [Fin.sum_univ_two]
    change (q.val + 1) + (l - q.val) + 1 = l + 2
    omega

/-- 概要：正長語の二部分割の共有位置（BF §1.2.4）。
方針：最初の部分長から一を引く。
規約：有限位置は元の語の範囲内。
使われ方：合成の二部分割から内側の辺切断点を復元する。 -/
def twoCut {l : ℕ} (hl : 0 < l) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition 2 l) : Fin l :=
  ⟨(r.val 0).val - 1, by
    have hp := r.positive hl 0
    have hb := (r.val 0).isLt
    omega⟩

/-- 概要：共有位置から作った二部分割は同じ位置へ戻る（BF §1.2.4）。
方針：最初の部分長 q+1 から一を引く。
規約：範囲の証明には依存しない。
使われ方：二部分割と切断点の有限同値の片側。 -/
lemma twoCut_two {l : ℕ} (hl : 0 < l) (q : Fin l) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.twoCut hl (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two q) = q := by
  apply Fin.ext
  change q.val + 1 - 1 = q.val
  omega

/-- 概要：共有位置を復元して作り直すと元の二部分割（BF §1.2.4）。
方針：正の第一部分長と二項の総長条件で両部分長を決める。
規約：有限関数の二点で比較する。
使われ方：二部分割と切断点の有限同値のもう片側。 -/
lemma two_twoCut {l : ℕ} (hl : 0 < l) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition 2 l) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.twoCut hl r) = r := by
  have hp := r.positive hl 0
  have hs := r.property.2
  rw [Fin.sum_univ_two] at hs
  apply Subtype.ext
  funext i
  apply Fin.ext
  fin_cases i
  · change (r.val 0).val - 1 + 1 = (r.val 0).val
    omega
  · change l - ((r.val 0).val - 1) = (r.val 1).val
    omega

/-- 概要：正長語の二部分割と共有位置の有限同値（BF §1.2.4）。
方針：第一部分長から共有位置を取り出し、二つの長さを復元する。
規約：任意の正の語長。
使われ方：部分合成の二部分割の和を内側切断点の和へ移す。 -/
def twoEquiv {l : ℕ} (hl : 0 < l) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition 2 l ≃ Fin l where
  toFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.twoCut hl
  invFun := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two
  left_inv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two_twoCut hl
  right_inv := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.twoCut_two hl

/-- 概要：二部分割の後半は共有位置から始まる（BF §1.2.4）。
方針：先行する第一部分長−1 の和を評価する。
規約：零始まりの共有位置。
使われ方：二段切断の出力頂点の位置比較。 -/
lemma two_start_one {l : ℕ} (q : Fin l) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two q).start 1 = q.val := by
  change (q.val + 1 - 1) + 0 = q.val
  omega

/-- 概要：二部分割の前半は共有位置を含む接頭語（BF §1.2.4）。
方針：最初の開始位置零と第一部分長を使う。
規約：共有位置を前半の最後に含める。
使われ方：合成語の最初の挿入部分の実際の列。 -/
lemma two_segment_zero {α : Type*} {l : ℕ} (q : Fin l) (v : Fin l → α) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two q).segment v 0 = (List.ofFn v).take (q.val + 1) := by
  change ((List.ofFn v).drop 0).take (q.val + 1) = _
  rw [List.drop_zero]

/-- 概要：二部分割の後半は共有位置を含む接尾語（BF §1.2.4）。
方針：第二開始位置と残りの正確な語長で take を消す。
規約：共有位置を後半の先頭に含める。
使われ方：合成語の二つ目の挿入部分の実際の列。 -/
lemma two_segment_one {α : Type*} {l : ℕ} (q : Fin l) (v : Fin l → α) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two q).segment v 1 = (List.ofFn v).drop q.val := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.two_start_one]
  change ((List.ofFn v).drop q.val).take (l - q.val) = _
  exact List.take_of_length_le (by simp only [List.length_drop, List.length_ofFn, le_refl])

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition

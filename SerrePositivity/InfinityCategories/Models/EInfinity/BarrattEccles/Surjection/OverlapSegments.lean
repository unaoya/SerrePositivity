module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
模型。文献の定義との比較は後で
# 端点を重ねた分割の部分語と範囲

概要：Berger–Fresse §1.2.4 の分割添字から内側語の実際の部分語を切り出す。
方針：先行する長さ−1 の部分和と、部分長の総和を比較する。
規約：空語の一部分割も扱う。
使われ方：χ の部分合成の語と、その正しい次数を構成する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition

variable {t l : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t l)

/-- 概要：部分語の開始位置＋部分長は元の語長以下（BF §1.2.4）。
方針：先行するステップと現在ステップの総和を全ステップの和で抑える。
規約：内側が空の場合は部分長も零。
使われ方：drop の後の take が指定した部分長を持つことを示す。 -/
lemma start_add_length_le (i : Fin t) : r.start i + (r.val i).val ≤ l := by
  by_cases hl : l = 0
  · subst l
    have hz : ∀ j, (r.val j).val = 0 := by intro j; have := (r.val j).isLt; omega
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.start, hz, Nat.zero_sub, List.ofFn_const, List.take_replicate,
      List.sum_replicate, nsmul_zero, Nat.add_zero, Nat.le_refl]
  · have hlpos : 0 < l := by omega
    let xs := List.ofFn (fun j => (r.val j).val - 1)
    have hib : i.val < xs.length := by simpa only [xs, List.length_ofFn] using i.isLt
    have hb := List.sum_take_add_sum_drop xs (i.val + 1)
    rw [List.take_succ_eq_append_getElem hib, List.sum_append] at hb
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at hb
    have hget : xs[i.val] = (r.val i).val - 1 := by simp only [xs, List.getElem_ofFn]
    rw [hget] at hb
    have hs : xs.sum + 1 = l := by simpa only [xs, List.sum_ofFn] using r.sum_steps hlpos
    have hp := r.positive hlpos i
    change (xs.take i.val).sum + (r.val i).val ≤ l
    omega

/-- 概要：内側語の指定した部分語（BF §1.2.4）。
方針：開始位置で drop し指定した部分長を take する。
規約：位置と値の型を区別し、値の型は任意。
使われ方：各指定値の出現を置き換えるリスト。 -/
def segment {α : Type*} (v : Fin l → α) (i : Fin t) : List α :=
  ((List.ofFn v).drop (r.start i)).take (r.val i).val

/-- 概要：切り出した部分語の長さは指定した部分長（BF §1.2.4）。
方針：開始位置と部分長の上界を drop と take の長さへ適用する。
規約：空語の部分語の長さは零。
使われ方：合成語の総長を計算する。 -/
@[simp] lemma segment_length {α : Type*} (v : Fin l → α) (i : Fin t) :
    (r.segment v i).length = (r.val i).val := by
  have hb := r.start_add_length_le i
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment, List.length_take, List.length_drop, List.length_ofFn]
  omega

/-- 概要：全ての部分語を出現順に並べたリスト（BF §1.2.4）。
方針：有限部分語添字を ofFn で列挙する。
規約：隣り合う部分語の境界値は両方に現れる。
使われ方：外側語の指定値の全出現へ順に代入する。 -/
def segments {α : Type*} (v : Fin l → α) : List (List α) :=
  List.ofFn (r.segment v)

/-- 概要：部分語列の個数は指定された分割数（BF §1.2.4）。
方針：ofFn の長さを評価する。
規約：空語の場合にも成立する。
使われ方：指定値の出現回数と代入する部分語の個数を揃える。 -/
@[simp] lemma segments_length {α : Type*} (v : Fin l → α) :
    (r.segments v).length = t := List.length_ofFn

/-- 概要：部分語列の平坦化の長さは元の語長＋共有端点数（BF §1.2.4）。
方針：各部分語の長さと分割の総長条件を使う。
規約：分割数が正の合成で使う。
使われ方：χ の合成語の次数を入力次数の和と同定する。 -/
lemma segments_flatten_length {α : Type*} (v : Fin l → α) :
    (r.segments v).flatten.length = l + t - 1 := by
  simp only [List.length_flatten, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segments, List.map_ofFn, Function.comp_apply,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition.segment_length, List.sum_ofFn]
  exact r.sum_lengths

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition

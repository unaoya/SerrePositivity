module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesuras
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Sort

/-!
模型。文献の定義との比較は後で
# 部分合成で指定する値の出現順

概要：Berger–Fresse §1.2.4–5 の指定値の出現を語の位置の順で列挙する。
方針：全位置の昇順リストを値の一致で切り、部分語数と同じ有限添字で読む。
規約：出現回数はリスト化した語の count とする。
使われ方：部分合成の各挿入部分語と外側の行次数の符号を対応させる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：指定値の出現回数（BF §1.2.4）。
方針：語をリストにして count を使う。
規約：全射性は要求しない。
使われ方：内側語の重なる分割の部分語数を指定する。 -/
def occurrenceCount {n l : ℕ} (v : Fin l → Fin n) (k : Fin n) : ℕ :=
  (List.ofFn v).count k

/-- 概要：指定値の出現位置の昇順リスト（BF §1.2.4）。
方針：全有限位置から値の一致する位置だけを取る。
規約：出現位置の順であり値の順ではない。
使われ方：出現に対応する外側語の行次数を読む。 -/
def occurrencePositions {n l : ℕ} (v : Fin l → Fin n) (k : Fin n) : List (Fin l) :=
  (List.finRange l).filter (fun i => v i = k)

/-- 概要：昇順に列挙した出現位置の長さは出現回数（BF §1.2.4）。
方針：ofFn の map 表示で文字の count を位置の filter の長さへ直す。
規約：任意の有限語に適用する。
使われ方：部分語と出現位置に同じ有限添字を使う。 -/
lemma occurrencePositions_length {n l : ℕ} (v : Fin l → Fin n) (k : Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrencePositions v k).length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrencePositions
  rw [List.count_eq_countP, List.ofFn_eq_map, List.countP_map, List.countP_eq_length_filter]
  congr 1

/-- 概要：第 j 出現の実際の位置（BF §1.2.5）。
方針：昇順の出現位置リストを有限添字で読む。
規約：番号は零始まり。
使われ方：成分の交換符号で外側の指定出現の行番号を使う。 -/
def occurrenceAt {n l : ℕ} (v : Fin l → Fin n) (k : Fin n)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k)) : Fin l :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrencePositions v k).get ⟨j.val, by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrencePositions_length]; exact j.isLt⟩

/-- 概要：列挙した出現位置は指定値を持つ（BF §1.2.4）。
方針：filter されたリストの所属条件を取り出す。
規約：全射性は使わない。
使われ方：符号の添字が本当に指定値の出現であることを保証する。 -/
lemma occurrenceAt_value {n l : ℕ} (v : Fin l → Fin n) (k : Fin n)
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v k)) : v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k j) = k := by
  have hm := List.get_mem (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrencePositions v k)
    ⟨j.val, by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrencePositions_length]; exact j.isLt⟩
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt, decide_eq_true_eq] using (List.mem_filter.mp hm).2

/-- 概要：全射語の各値の出現回数は正（BF §1.2.4）。
方針：全射性からリストの所属を得て count の正値性へ移す。
規約：指定値がある arity で成立する。
使われ方：部分合成の分割数は必ず正となる。 -/
lemma occurrenceCount_pos {n l : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (k : Fin n) :
    0 < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount v.val k := by
  apply List.count_pos_iff.mpr
  obtain ⟨i, hi⟩ := v.surjective k
  exact List.mem_ofFn.mpr ⟨i, hi⟩

/-- 概要：出現の列挙は狭義単調（BF §1.2.5）。
方針：全位置の昇順リストの部分列であることを使う。
規約：位置を自然な Fin の順序で比較する。
使われ方：外側成分の次数と符号の計算を出現順に行う。 -/
lemma occurrenceAt_strictMono {n l : ℕ} (v : Fin l → Fin n) (k : Fin n) :
    StrictMono (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceAt v k) := by
  have hs : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrencePositions v k).SortedLT := by
    rw [List.sortedLT_iff_pairwise]
    exact (List.sortedLT_finRange l).pairwise.filter _
  intro i j hij
  exact hs.strictMono_get hij

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

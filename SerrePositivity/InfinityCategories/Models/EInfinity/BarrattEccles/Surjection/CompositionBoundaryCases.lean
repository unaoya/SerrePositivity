module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Composition
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapSingle

/-!
模型。文献の定義との比較は後で
# 合成の次数零の符号と空語の境界分岐

概要：Berger–Fresse §1.2.4–5 の次数零と nullary の合成を定義から計算する。
方針：次数零では内側の区切りがなく、空語の分割は一出現の場合に限る。
規約：零 arity を除外して部分合成を定義しない。
使われ方：単位・零入力の保存則と原典の符号例を検証する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：次数零の全射語の任意の上界で行番号は零（BF §1.2.2・§1.2.5）。
方針：有限自己全射の単射性から後の同値の出現を排除する。
規約：上界は語長を超えてもよい。
使われ方：次数零の内側語との合成の符号を計算する。 -/
lemma lineRank_degree_zero {n : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0) (p : ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v.val p = 0 := by
  have hi : Function.Injective v.val := Finite.injective_iff_surjective.mpr v.surjective
  have hc : ∀ j, ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val j := by
    rintro j ⟨k, hjk, hv⟩
    have he := hi hv
    subst k
    exact (lt_irrefl j) hjk
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank, hc, and_false, Finset.filter_false, Finset.card_empty]

/-- 概要：次数零の内側語との合成の全ての符号は正（BF §1.2.5）。
方針：内側の全成分の行次数を零にする。
規約：内側の空語も含む。
使われ方：次数零・空入力の符号の境界条件を確認する。 -/
@[simp] lemma compositionSign_inner_degree_zero {m n d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 0) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + 0)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign u v k r = 1 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionExponent, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.segmentDegree, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank_degree_zero,
    Nat.sub_zero, zero_mul, Finset.sum_const_zero, pow_zero]

/-- 概要：次数零の外側語との合成の全ての符号は正（BF §1.2.5）。
方針：外側の後続成分の総次数は零。
規約：内側の次数は任意。
使われ方：置換の合成との比較と左単位の符号を確認する。 -/
@[simp] lemma compositionSign_outer_degree_zero {m n e : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) 0) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e) (k : Fin (m + 1))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (n + e)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign u v k r = 1 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionExponent, Nat.zero_sub, mul_zero,
    Finset.sum_const_zero, pow_zero]

/-- 概要：指定値が一回以外に現れる場合の空語の挿入は零（BF §1.2.4 の空語拡張）。
方針：空語を分割できるのは一部分の場合だけなので有限和の添字が空。
規約：nullary の次数零の基底をそのまま入力に取る。
使われ方：空語の挿入の保存則を出現回数で分ける。 -/
lemma compositionOnWords_nullary_of_count_ne_one (A : Type u) [CommRing A] {m d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (k : Fin (m + 1))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k ≠ 1) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A u v k = 0 := by
  let hempty : IsEmpty (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount u.val k) (0 + 0)) :=
    ⟨fun r => h r.count_eq_one_of_empty⟩
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords
  exact Fintype.sum_empty _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

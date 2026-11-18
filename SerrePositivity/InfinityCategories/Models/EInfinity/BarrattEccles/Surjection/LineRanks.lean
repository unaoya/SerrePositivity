module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSigns

/-!
模型。文献の定義との比較は後で
# 全射語の最後の行番号と次数

概要：Berger–Fresse §1.2.2・§1.2.5 の成分次数の和の終端を元の次数に同定する。
方針：最後の位置より前には全ての区切りがあり、その個数は次数に等しい。
規約：零 arity の空語も含む。
使われ方：内側・外側の成分次数の総和と shuffle 経路の辺数を照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：最初の位置の行番号は零（BF §1.2.2・§1.2.5）。
方針：零より前の有限位置は存在しない。
規約：空語も含む。
使われ方：成分次数の望遠鏡和の始端を消す。 -/
@[simp] lemma lineRank_zero {n l : ℕ} (v : Fin l → Fin n) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v 0 = 0 := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank, Nat.not_lt_zero, false_and, Finset.filter_false, Finset.card_empty]

/-- 概要：全射語の最後の行番号は次数に等しい（BF §1.2.2・§1.2.5）。
方針：各区切りはより後の出現を持つため最終位置より前であり、全区切りを数える。
規約：空語では両辺は零。
使われ方：成分次数の全和を元の次数へ戻す。 -/
lemma lineRank_last {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank v.val (n + d - 1) = d := by
  have he : Finset.univ.filter (fun j : Fin (n + d) =>
      j.val < n + d - 1 ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val j) = Finset.univ.filter (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura v.val) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.right
    · intro h
      have hc := h
      obtain ⟨k, hjk, _⟩ := h
      have hb := k.isLt
      change j.val < k.val at hjk
      exact ⟨by omega, hc⟩
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.lineRank
  rw [he]
  simpa only [Fintype.card_subtype] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.card_caesuras_basisWord v

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

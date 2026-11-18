module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeCuts

/-!
模型。文献の定義との比較は後で
# 非退化な切断と左右の語の単射性

概要：Berger–Fresse §2.2.1 の非零な Δ¹ の切断を元の語の位置で特徴付ける。
方針：零頂点を持つ左側と一頂点を持つ右側を別々に比較する。
規約：切断点は左右の両方に含み、同じ文字がその位置に一度だけ現れる。
使われ方：切断の境界を語の削除項へ対応させる。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：展開した位置は左側か右側の元位置で表せる（BF §2.2.1）。
方針：切断点以下なら同じ位置、それより後なら一を引く。
規約：切断点の二つの展開位置を左右で一つずつ持つ。
使われ方：非退化性を左右の語へ戻す。 -/
lemma edgePosition_cases {l : ℕ} (p : Fin l) (q : Fin (l + 1)) :
    (∃ i : Fin l, i ≤ p ∧ q = i.castSucc) ∨
      (∃ i : Fin l, p ≤ i ∧ q = i.succ) := by
  by_cases h : q.val ≤ p.val
  · left
    refine ⟨⟨q.val, by omega⟩, ?_, ?_⟩
    · exact h
    · rfl
  · right
    refine ⟨⟨q.val - 1, by omega⟩, ?_, ?_⟩
    · change p.val ≤ q.val - 1
      omega
    · apply Fin.ext
      simp only [Fin.val_succ]
      omega

/-- 概要：非退化な切断の左側で元の語は単射（BF §2.2.1）。
方針：同じ色と零頂点の一致を展開位置の単射性で消去する。
規約：切断点自身を含む。
使われ方：同じ色の二つの出現の片方を左側に固定する。 -/
lemma edge_left_injective {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (i j : Fin l) (hi : i ≤ p) (hj : j ≤ p)
    (hij : u i = u j) : i = j := by
  have he : i.castSucc = j.castSucc := h (by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_castSucc u p i hi, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_castSucc u p j hj, hij])
  exact Fin.ext (congrArg (fun q : Fin (l + 1) => q.val) he)

/-- 概要：非退化な切断の右側で元の語は単射（BF §2.2.1）。
方針：同じ色と一頂点の一致を展開位置の単射性で消去する。
規約：切断点自身を含む。
使われ方：同じ色の二つの出現の片方を右側に固定する。 -/
lemma edge_right_injective {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) (i j : Fin l) (hi : p ≤ i) (hj : p ≤ j)
    (hij : u i = u j) : i = j := by
  have he : i.succ = j.succ := h (by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_succ u p i hi, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_succ u p j hj, hij])
  apply Fin.ext
  have := congrArg (fun q : Fin (l + 1) => q.val) he
  simpa only [Fin.val_succ, Nat.add_left_inj] using this

/-- 概要：左右で単射であることは切断の非退化性と同値（BF §2.2.1）。
方針：展開位置を左右に分け、同じ側は単射性、異なる側は頂点値の不一致を使う。
規約：元の語の全射性や隣接非退化性は要求しない。
使われ方：削除・切断点の変更後の切断が非零であることを証明する。 -/
lemma edgeNondegenerate_iff {n l : ℕ} (u : Fin l → Fin n) (p : Fin l) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p ↔
      (∀ i j : Fin l, i ≤ p → j ≤ p → u i = u j → i = j) ∧
      (∀ i j : Fin l, p ≤ i → p ≤ j → u i = u j → i = j) := by
  constructor
  · intro h
    exact ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective h, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_right_injective h⟩
  · rintro ⟨hL, hR⟩ a b hab
    rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePosition_cases p a with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
      rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePosition_cases p b with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_castSucc u p i hi, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_castSucc u p j hj] at hab
      exact congrArg Fin.castSucc (hL i j hi hj (congrArg Prod.fst hab))
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_castSucc u p i hi, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_succ u p j hj] at hab
      have hv := congrArg (fun t : Fin n × Fin 2 => t.2.val) hab
      change (0 : ℕ) = 1 at hv
      omega
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_succ u p i hi, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_castSucc u p j hj] at hab
      have hv := congrArg (fun t : Fin n × Fin 2 => t.2.val) hab
      change (1 : ℕ) = 0 at hv
      omega
    · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_succ u p i hi, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgePair_succ u p j hj] at hab
      exact congrArg Fin.succ (hR i j hi hj (congrArg Prod.fst hab))

/-- 概要：同じ文字の二つの出現は切断点を厳密に跨ぐ（BF §2.2.1）。
方針：同じ側なら左右の単射性に矛盾する。
規約：出現の順序 i<j を指定する。
使われ方：反復色の辺の境界を二つの削除位置に対応させる。 -/
lemma repeated_straddles {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) {i j : Fin l} (hij : i < j) (hu : u i = u j) :
    i < p ∧ p < j := by
  constructor
  · by_contra hip
    have hp := le_of_not_gt hip
    exact (ne_of_lt hij) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_right_injective h i j hp (le_trans hp hij.le) hu)
  · by_contra hpj
    have hjp := le_of_not_gt hpj
    exact (ne_of_lt hij) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective h i j (le_trans hij.le hjp) hjp hu)

/-- 概要：非退化な辺の切断では全ての区切りが切断点より前にある（BF §2.2.3–4）。
方針：後の同色出現との組に切断点を跨ぐ性質を適用する。
規約：切断点自身は区切りではない。
使われ方：位置符号を零へ簡約する。 -/
lemma caesura_before_pivot {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) {i : Fin l} (hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i) : i < p := by
  obtain ⟨j, hij, hji⟩ := hi
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.repeated_straddles h hij hji.symm).1

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

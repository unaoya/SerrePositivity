module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletion

/-!
模型。文献の定義との比較は後で
# 削除後だけ非零となる切断の障害

概要：Berger–Fresse §2.2.7 の逆向きの削除項で元切断が退化する場合を特徴付ける。
方針：削除位置を除けば左右で単射なので、障害は削除文字と同じ側の同色出現だけである。
規約：元の切断点は削除後の切断点の succAbove による像。
使われ方：余分な削除項の相殺相手を一意に取り出す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：二つの元位置が切断点の同じ側にある条件（BF §2.2.7）。
方針：両方が左側か両方が右側であると定める。
規約：切断点は両方の側に含まれる。
使われ方：元の退化切断の重複が生じる側を記述する。 -/
def SameCutSide {l : ℕ} (p a b : Fin l) : Prop :=
  (a ≤ p ∧ b ≤ p) ∨ (p ≤ a ∧ p ≤ b)

/-- 概要：同じ側の条件は有限に判定できる（BF §2.2.7）。
方針：有限順序の二つの不等式を判定する。
規約：計算可能な判定を使う。
使われ方：削除項の障害の有限部分型。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instDecidableSameCutSide {l : ℕ} (p a b : Fin l) : Decidable (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide p a b) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide
  infer_instance

/-- 概要：同じ側の条件は対称（BF §2.2.7）。
方針：各側の二つの不等式を交換する。
規約：切断点を固定する。
使われ方：削除位置が等値対のどちらに現れるかを交換する。 -/
lemma sameCutSide_symm {l : ℕ} {p a b : Fin l} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide p a b) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide p b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- 概要：左にある位置と同じ側にあることは左側に属すること（BF §2.2.7）。
方針：右側の分岐を厳密な不等式で排除する。
規約：最初の位置は切断点そのものではない。
使われ方：障害位置の一意性。 -/
lemma sameCutSide_left_iff {l : ℕ} (p a b : Fin l) (ha : a < p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide p a b ↔ b ≤ p := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide, ha.le, not_le_of_gt ha]

/-- 概要：右にある位置と同じ側にあることは右側に属すること（BF §2.2.7）。
方針：左側の分岐を厳密な不等式で排除する。
規約：切断点自身はどちらの分岐でも同じ。
使われ方：障害位置の一意性。 -/
lemma sameCutSide_right_iff {l : ℕ} (p a b : Fin l) (ha : p < a) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide p a b ↔ p ≤ b := by
  simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide, ha.le, not_le_of_gt ha]

/-- 概要：削除後の非零切断は削除位置以外で元の同じ側の単射性を与える（BF §2.2.7）。
方針：二つの元位置を削除の順序単射で戻して、削除後の左右単射性を使う。
規約：元切断自体の非零性は要求しない。
使われ方：逆の削除項の退化の原因を削除文字へ限定する。 -/
lemma erase_same_side_injective {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q)
    (a b : Fin (l + 1)) (hai : a ≠ i) (hbi : b ≠ i)
    (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide (i.succAbove q) a b) (hu : u a = u b) : a = b := by
  obtain ⟨x, hx⟩ := Fin.exists_succAbove_eq hai
  obtain ⟨y, hy⟩ := Fin.exists_succAbove_eq hbi
  have huv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i x = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i y := by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply, hx, hy] using hu
  have hxy : x = y := by
    rcases hs with hs | hs
    · apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective h x y _ _ huv
      · apply (Fin.strictMono_succAbove i).le_iff_le.mp
        simpa only [hx] using hs.1
      · apply (Fin.strictMono_succAbove i).le_iff_le.mp
        simpa only [hy] using hs.2
    · apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_right_injective h x y _ _ huv
      · apply (Fin.strictMono_succAbove i).le_iff_le.mp
        simpa only [hx] using hs.1
      · apply (Fin.strictMono_succAbove i).le_iff_le.mp
        simpa only [hy] using hs.2
  simpa only [hx, hy] using congrArg i.succAbove hxy

/-- 概要：削除後が非零なら、元切断の非零性は削除文字の同じ側の一意性と同値（BF §2.2.7）。
方針：元の同じ側の等値対が削除位置を含むかどうかで分ける。
規約：他の色の重複は既に削除後の非退化性で排除されている。
使われ方：元切断が退化する場合の具体的な障害位置を構成する。 -/
lemma original_cut_iff_no_same_side_repeat {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u (i.succAbove q) ↔
      ∀ j, u j = u i → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide (i.succAbove q) i j → j = i := by
  constructor
  · intro ho j hu hs
    rcases hs with hs | hs
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective ho j i hs.2 hs.1 hu
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_right_injective ho j i hs.2 hs.1 hu
  · intro hi
    have H (a b : Fin (l + 1)) (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide (i.succAbove q) a b)
        (hu : u a = u b) : a = b := by
      by_cases hai : a = i
      · subst a
        exact (hi b hu.symm hs).symm
      by_cases hbi : b = i
      · subst b
        exact hi a hu (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sameCutSide_symm hs)
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_same_side_injective u i q h a b hai hbi hs hu
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_iff]
    exact ⟨fun a b ha hb hu => H a b (Or.inl ⟨ha, hb⟩) hu,
      fun a b ha hb hu => H a b (Or.inr ⟨ha, hb⟩) hu⟩

/-- 概要：削除後だけ非零となる元切断の障害位置（BF §2.2.7）。
方針：削除位置以外で、同じ色を持ち、同じ側にある位置を指定する。
規約：障害位置は元の切断点そのものでもよい。
使われ方：反復相殺と切断点の項を区別する。 -/
def CutDeletionDefect {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (j : Fin (l + 1)) : Prop :=
  j ≠ i ∧ u j = u i ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide (i.succAbove q) i j

/-- 概要：削除障害の条件は有限に判定できる（BF §2.2.7）。
方針：位置・色・同じ側の条件をそれぞれ判定する。
規約：元切断の非零性を追加で仮定しない。
使われ方：具体的な余分削除項の検証と添字の部分集合。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instDecidableCutDeletionDefect {n l : ℕ} (u : Fin (l + 1) → Fin n) (i : Fin (l + 1)) (q : Fin l)
    (j : Fin (l + 1)) : Decidable (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u i q j) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect
  infer_instance

/-- 概要：削除後だけ非零であることは障害位置の存在と同値（BF §2.2.7）。
方針：元切断の非零性の特徴付けを否定する。
規約：削除後の切断の非零性を仮定する。
使われ方：逆向きの全削除項を元切断が非零の部分と障害を持つ部分へ分ける。 -/
lemma cutDeletionDefect_exists_iff {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q) :
    (∃ j, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u i q j) ↔ ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u (i.succAbove q) := by
  classical
  constructor
  · rintro ⟨j, hj, hu, hs⟩ ho
    exact hj ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.original_cut_iff_no_same_side_repeat u i q h).mp ho j hu hs)
  · intro ho
    by_contra hn
    apply ho
    apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.original_cut_iff_no_same_side_repeat u i q h).mpr
    intro j hu hs
    by_contra hj
    exact hn ⟨j, hj, hu, hs⟩

/-- 概要：削除後だけ非零となる元切断の障害位置は一意（BF §2.2.7）。
方針：削除文字と同じ側にある二障害を削除後の単射性で比較する。
規約：切断点を残すため削除位置は切断点とは異なる。
使われ方：相殺相手の選択を一意にする。 -/
lemma cutDeletionDefect_unique {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q)
    (a b : Fin (l + 1)) (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u i q a) (hb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutDeletionDefect u i q b) :
    a = b := by
  have hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide (i.succAbove q) a b := by
    rcases lt_or_gt_of_ne (Fin.ne_succAbove i q) with hi | hi
    · exact Or.inl ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sameCutSide_left_iff _ _ _ hi).mp ha.2.2,
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sameCutSide_left_iff _ _ _ hi).mp hb.2.2⟩
    · exact Or.inr ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sameCutSide_right_iff _ _ _ hi).mp ha.2.2,
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sameCutSide_right_iff _ _ _ hi).mp hb.2.2⟩
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_same_side_injective u i q h a b ha.1 hb.1 hs (ha.2.1.trans hb.2.1.symm)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

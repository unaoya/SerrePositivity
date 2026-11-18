module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapOutputs
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CutConvexity

/-!
模型。文献の定義との比較は後で
# 隙間切断の非退化性と隣接切断

概要：Berger–Fresse §2.2.7 の切断点障害項を、各文字を一度だけ置く隙間の側から分類する。
方針：左右の単射性を隙間の前後で定義し、隣接切断が零となる理由を反対側の同色へ限定する。
規約：全射性も元の辺切断の存在も仮定しない。
使われ方：非零の元切断がない場合も含めた切断点障害の相殺。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

/-- 概要：隙間の左右で色が単射である条件（BF §2.2.7）。
方針：各文字を隙間の前か後へ一度だけ置く。
規約：隙間の左は厳密不等号、右は広義不等号。
使われ方：切断点障害の削除項が集まる共通の隙間。 -/
def GapNondegenerate {n l : ℕ} (u : Fin l → Fin n) (q : Fin (l + 1)) : Prop :=
  (∀ i j, i.val < q.val → j.val < q.val → u i = u j → i = j) ∧
    (∀ i j, q.val ≤ i.val → q.val ≤ j.val → u i = u j → i = j)

/-- 概要：隙間の非退化性は有限に判定できる（BF §2.2.7）。
方針：全位置対の左右所属と色を比較する。
規約：選択公理を使わない。
使われ方：隙間の全有限和と具体的な監査。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.instDecidableGapNondegenerate {n l : ℕ} (u : Fin l → Fin n) (q : Fin (l + 1)) :
    Decidable (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u q) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate
  infer_instance

/-- 概要：非退化な隙間は全ての同色対の間に入る（BF §2.2.7）。
方針：同じ側の同色対を左右単射性で排除する。
規約：隙間番号は前の位置より大きく、後の位置以下。
使われ方：隙間と辺切断の境界条件の比較。 -/
lemma gapNondegenerate_iff_straddles {n l : ℕ} (u : Fin l → Fin n) (q : Fin (l + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u q ↔ ∀ i j, i < j → u i = u j → i.val < q.val ∧ q.val ≤ j.val := by
  constructor
  · intro h i j hij hu
    constructor
    · by_contra hi
      have hi' := le_of_not_gt hi
      exact (ne_of_lt hij) (h.2 i j hi' (le_trans hi' hij.le) hu)
    · by_contra hj
      have hj' := lt_of_not_ge hj
      exact (ne_of_lt hij) (h.1 i j (lt_trans hij hj') hj' hu)
  · intro h
    constructor
    · intro i j hi hj hu
      by_contra he
      rcases lt_or_gt_of_ne he with hij | hji
      · exact (not_le_of_gt hj) (h i j hij hu).2
      · exact (not_le_of_gt hi) (h j i hji hu.symm).2
    · intro i j hi hj hu
      by_contra he
      rcases lt_or_gt_of_ne he with hij | hji
      · exact (not_lt_of_ge hi) (h i j hij hu).1
      · exact (not_lt_of_ge hj) (h j i hji hu.symm).1

/-- 概要：非零辺切断の直前の隙間は非退化（BF §2.2.7）。
方針：辺切断の左側を切断点未満へ制限する。
規約：右側には切断点を含む。
使われ方：切断点色の終点境界の隙間。 -/
lemma gapNondegenerate_before {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.castSucc := by
  exact ⟨fun i j hi hj hu => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_left_injective h i j (le_of_lt hi) (le_of_lt hj) hu,
    fun i j hi hj hu => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edge_right_injective h i j hi hj hu⟩

/-- 概要：非零辺切断の直後の隙間は非退化（BF §2.2.7）。
方針：辺切断の右側を切断点より後へ制限する。
規約：左側には切断点を含む。
使われ方：切断点色の始点境界の隙間。 -/
lemma gapNondegenerate_after {n l : ℕ} {u : Fin l → Fin n} {p : Fin l}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.succ := by
  apply (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapNondegenerate_iff_straddles u p.succ).mpr
  intro i j hij hu
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.repeated_straddles h hij hu
  change i.val < p.val + 1 ∧ p.val + 1 ≤ j.val
  have hi := Fin.lt_def.mp hs.1
  have hj := Fin.lt_def.mp hs.2
  omega

/-- 概要：直前隙間が非退化なら辺切断の非零性は左の同色不在と同値（BF §2.2.7）。
方針：左側へ切断点を一つ加えるときの単射性だけを判定する。
規約：隙間の右側は既に切断点を含む。
使われ方：右隣の辺切断が退化する原因を削除する左同色位置へ同定する。 -/
lemma edgeNondegenerate_iff_gap_before {n l : ℕ} (u : Fin l → Fin n) (p : Fin l)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.castSucc) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p ↔ ∀ i, i < p → u i ≠ u p := by
  constructor
  · intro he i hi hu
    exact (ne_of_lt hi) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique he i hu)
  · intro hp
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_iff]
    refine ⟨?_, fun i j hi hj hu => h.2 i j hi hj hu⟩
    intro i j hi hj hu
    by_cases hip : i = p
    · subst i
      by_contra hjp
      exact hp j (lt_of_le_of_ne hj (Ne.symm hjp)) hu.symm
    · by_cases hjp : j = p
      · subst j
        exact False.elim (hp i (lt_of_le_of_ne hi hip) hu)
      · have hi' : i < p := lt_of_le_of_ne hi hip
        have hj' : j < p := lt_of_le_of_ne hj hjp
        exact h.1 i j hi' hj' hu

/-- 概要：直後隙間が非退化なら辺切断の非零性は右の同色不在と同値（BF §2.2.7）。
方針：右側へ切断点を一つ加えるときの単射性だけを判定する。
規約：隙間の左側は既に切断点を含む。
使われ方：左隣の辺切断が退化する原因を削除する右同色位置へ同定する。 -/
lemma edgeNondegenerate_iff_gap_after {n l : ℕ} (u : Fin l → Fin n) (p : Fin l)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.succ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p ↔ ∀ i, p < i → u i ≠ u p := by
  constructor
  · intro he i hi hu
    exact (ne_of_gt hi) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_unique he i hu)
  · intro hp
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeNondegenerate_iff]
    refine ⟨?_, ?_⟩
    · intro i j hi hj hu
      apply h.1 i j (by change i.val < p.val + 1; exact Nat.lt_add_one_of_le hi)
        (by change j.val < p.val + 1; exact Nat.lt_add_one_of_le hj) hu
    · intro i j hi hj hu
      by_cases hip : i = p
      · subst i
        by_contra hjp
        exact hp j (lt_of_le_of_ne hj hjp) hu.symm
      · by_cases hjp : j = p
        · subst j
          exact False.elim (hp i (lt_of_le_of_ne hi (Ne.symm hip)) hu)
        · have hi' : p < i := lt_of_le_of_ne hi (Ne.symm hip)
          have hj' : p < j := lt_of_le_of_ne hj (Ne.symm hjp)
          apply h.2 i j (by change p.val + 1 ≤ i.val; exact Nat.add_one_le_of_lt hi')
            (by change p.val + 1 ≤ j.val; exact Nat.add_one_le_of_lt hj') hu

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

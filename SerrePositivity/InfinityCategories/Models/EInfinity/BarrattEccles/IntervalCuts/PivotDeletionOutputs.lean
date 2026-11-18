module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotDeletionGaps
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ResidualCutOutputs
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapTensors

/-!
模型。文献の定義との比較は後で
# 切断点障害の実際の削除出力と隙間値

概要：Berger–Fresse §2.2.7 の切断点障害の削除後の出力は元の語の隙間出力になる。
方針：削除位置の出現を同色の切断点へ交換し、左右の出現集合を比較する。
規約：左削除なら直前、右削除なら直後の隙間を使う。
使われ方：全削除和の切断点障害部分を実際の隙間テンソルで計算する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

private lemma pivot_left_occurrence {n l : ℕ} (u : Fin l → Fin n) (i p : Fin l)
    (hi : i < p) (hu : u i = u p) (k : Fin n) :
    (∃ a, a ≠ i ∧ a ≤ p ∧ u a = k) ↔ ∃ a, a < p ∧ u a = k := by
  constructor
  · rintro ⟨a, hai, ha, hua⟩
    by_cases hap : a = p
    · subst a
      exact ⟨i, hi, hu.trans hua⟩
    · exact ⟨a, lt_of_le_of_ne ha hap, hua⟩
  · rintro ⟨a, ha, hua⟩
    by_cases hai : a = i
    · subst a
      exact ⟨p, ne_of_gt hi, le_rfl, hu.symm.trans hua⟩
    · exact ⟨a, hai, ha.le, hua⟩

private lemma pivot_right_occurrence {n l : ℕ} (u : Fin l → Fin n) (i p : Fin l)
    (hi : p < i) (hu : u i = u p) (k : Fin n) :
    (∃ a, a ≠ i ∧ p ≤ a ∧ u a = k) ↔ ∃ a, p < a ∧ u a = k := by
  constructor
  · rintro ⟨a, hai, ha, hua⟩
    by_cases hap : a = p
    · subst a
      exact ⟨i, hi, hu.trans hua⟩
    · exact ⟨a, lt_of_le_of_ne ha (Ne.symm hap), hua⟩
  · rintro ⟨a, ha, hua⟩
    by_cases hai : a = i
    · subst a
      exact ⟨p, ne_of_lt hi, le_rfl, hu.symm.trans hua⟩
    · exact ⟨a, hai, ha.le, hua⟩

/-- 概要：切断点同色の左位置の削除出力は元切断点直前の隙間出力（BF §2.2.7）。
方針：左側では削除位置と切断点の同色出現を交換し、右側はそのまま保つ。
規約：出力頂点集合の等式には非退化性は不要。
使われ方：左の切断点障害削除項の値を隙間値へ移す。 -/
lemma edgeOutputVertices_erase_pivot_before {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (hi : i < i.succAbove q)
    (hu : u i = u (i.succAbove q)) (k : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices u (i.succAbove q).castSucc k := by
  ext b
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_mem_iff, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices_mem_iff,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_left_occurrence_excluding, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_right_occurrence_excluding,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_left_occurrence u i _ hi hu k]
  have hr : (∃ a, a ≠ i ∧ i.succAbove q ≤ a ∧ u a = k) ↔
      ∃ a, i.succAbove q ≤ a ∧ u a = k := by
    constructor
    · rintro ⟨a, _, ha, hua⟩
      exact ⟨a, ha, hua⟩
    · rintro ⟨a, ha, hua⟩
      exact ⟨a, fun he => (not_le_of_gt hi) (he ▸ ha), ha, hua⟩
  rw [hr]
  rfl

/-- 概要：切断点同色の右位置の削除出力は元切断点直後の隙間出力（BF §2.2.7）。
方針：右側では削除位置と切断点の同色出現を交換し、左側はそのまま保つ。
規約：出力頂点集合の等式には非退化性は不要。
使われ方：右の切断点障害削除項の値を隙間値へ移す。 -/
lemma edgeOutputVertices_erase_pivot_after {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (hi : i.succAbove q < i)
    (hu : u i = u (i.succAbove q)) (k : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices u (i.succAbove q).succ k := by
  ext b
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_mem_iff, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutputVertices_mem_iff,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_left_occurrence_excluding, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_right_occurrence_excluding,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivot_right_occurrence u i _ hi hu k]
  have hl : (∃ a, a ≠ i ∧ a ≤ i.succAbove q ∧ u a = k) ↔
      ∃ a, a ≤ i.succAbove q ∧ u a = k := by
    constructor
    · rintro ⟨a, _, ha, hua⟩
      exact ⟨a, ha, hua⟩
    · rintro ⟨a, ha, hua⟩
      exact ⟨a, fun he => (not_le_of_gt hi) (he ▸ ha), ha, hua⟩
  rw [hl]
  simp only [Fin.val_succ, Nat.lt_add_one_iff, Nat.add_one_le_iff]
  rfl

/-- 概要：切断点障害の非零削除項の実際の全射基底語（BF §2.2.7）。
方針：残る切断点が削除色を保持し、非零切断が削除語の非退化性を与える。
規約：元の語次数 d+1 から d へ移る。
使われ方：切断点障害の削除和の実際の基底評価。 -/
def pivotEraseBasisWord {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (i : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val i) q) (hu : u.val i = u.val (i.succAbove q)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d :=
  ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val i, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_surjective_iff u.val u.surjective i).mpr
    ⟨i.succAbove q, Fin.succAbove_ne i q, hu.symm⟩,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nondegenerate_of_edgeNondegenerate h⟩

/-- 概要：左の切断点障害削除語の全出力族は元の直前隙間族（BF §2.2.7）。
方針：各色の頂点集合の等式を単体族へ持ち上げる。
規約：両族は実際の区間単体に値を取る。
使われ方：左削除項のテンソル値と次数の照合。 -/
lemma pivotErase_output_before {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (i : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val i) q) (hu : u.val i = u.val (i.succAbove q))
    (hi : i < i.succAbove q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotEraseBasisWord u i q h hu) q = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutput u (i.succAbove q).castSucc := by
  funext k
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_erase_pivot_before u.val i q hi hu k

/-- 概要：右の切断点障害削除語の全出力族は元の直後隙間族（BF §2.2.7）。
方針：各色の頂点集合の等式を単体族へ持ち上げる。
規約：両族は実際の区間単体に値を取る。
使われ方：右削除項のテンソル値と次数の照合。 -/
lemma pivotErase_output_after {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (i : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val i) q) (hu : u.val i = u.val (i.succAbove q))
    (hi : i.succAbove q < i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotEraseBasisWord u i q h hu) q = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutput u (i.succAbove q).succ := by
  funext k
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_erase_pivot_after u.val i q hi hu k

/-- 概要：左の切断点障害削除項の実際のテンソル値は元の直前隙間値（BF §2.2.7）。
方針：全出力族の一致を共通次数の反復テンソルへ渡す。
規約：元の語次数 d+1 と同じ出力次数。
使われ方：全削除和を隙間値で表す。 -/
lemma pivotErase_tensor_before (A : Type u) [CommRing A] {n d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) (i : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val i) q) (hu : u.val i = u.val (i.succAbove q))
    (hi : i < i.succAbove q) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n (d + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotEraseBasisWord u i q h hu) q)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ h) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u (i.succAbove q).castSucc := by
  have hf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotErase_output_before u i q h hu hi
  have hd : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutput u (i.succAbove q).castSucc) = d + 1 := by
    rw [← hf]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ h
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor_eq A u _ hd]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_congr A n _ _ (-((d + 1 : ℕ) : ℤ))
    (congrArg (fun r : ℕ => -(r : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ h))
    (congrArg (fun r : ℕ => -(r : ℤ)) hd) hf

/-- 概要：右の切断点障害削除項の実際のテンソル値は元の直後隙間値（BF §2.2.7）。
方針：全出力族の一致を共通次数の反復テンソルへ渡す。
規約：元の語次数 d+1 と同じ出力次数。
使われ方：全削除和を隙間値で表す。 -/
lemma pivotErase_tensor_after (A : Type u) [CommRing A] {n d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) (i : Fin (n + (d + 1))) (q : Fin (n + d))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val i) q) (hu : u.val i = u.val (i.succAbove q))
    (hi : i.succAbove q < i) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n (d + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotEraseBasisWord u i q h hu) q)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ h) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor A u (i.succAbove q).succ := by
  have hf := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.pivotErase_output_after u i q h hu hi
  have hd : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tupleDegree n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapOutput u (i.succAbove q).succ) = d + 1 := by
    rw [← hf]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ h
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapTensor_eq A u _ hd]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_congr A n _ _ (-((d + 1 : ℕ) : ℤ))
    (congrArg (fun r : ℕ => -(r : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ h))
    (congrArg (fun r : ℕ => -(r : ℤ)) hd) hf

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

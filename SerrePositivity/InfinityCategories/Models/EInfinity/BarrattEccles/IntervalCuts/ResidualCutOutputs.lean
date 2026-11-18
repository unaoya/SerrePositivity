module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ResidualCutInvolution
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.DeletedOutputVertices
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.TensorDegreeTransport

/-!
模型。文献の定義との比較は後で
# 交換相手の削除切断の出力一致

概要：Berger–Fresse §2.2.7 の非切断点障害の交換対で全出力と実際のテンソル値を一致させる。
方針：同色・同側の二位置のどちらを除いても、各側の各色の出現の有無は変わらない。
規約：符号の反対性は別に証明し、この段階では全出力の値を比較する。
使われ方：固定点なし対合による余分な削除項の相殺。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：削除後の左側出現は削除位置以外の元の左側出現（BF §2.2.7）。
方針：削除の順序単射で存在位置を前後に移す。
規約：指定色は削除色でもよい。
使われ方：交換する削除位置に依存しない零頂点の所属。 -/
lemma erase_left_occurrence_excluding {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (k : Fin n) :
    (∃ a : Fin l, a ≤ q ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i a = k) ↔
      ∃ b : Fin (l + 1), b ≠ i ∧ b ≤ i.succAbove q ∧ u b = k := by
  constructor
  · rintro ⟨a, ha, hu⟩
    exact ⟨i.succAbove a, Fin.succAbove_ne i a, (Fin.strictMono_succAbove i).monotone ha, hu⟩
  · rintro ⟨b, hbi, hb, hu⟩
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hbi
    refine ⟨a, ?_, ?_⟩
    · apply (Fin.strictMono_succAbove i).le_iff_le.mp
      rwa [ha]
    · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply, ha] using hu

/-- 概要：削除後の右側出現は削除位置以外の元の右側出現（BF §2.2.7）。
方針：削除の順序単射の順序保存と反映を使う。
規約：切断点も右側に含める。
使われ方：交換対の一頂点の所属を比較する。 -/
lemma erase_right_occurrence_excluding {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i : Fin (l + 1)) (q : Fin l) (k : Fin n) :
    (∃ a : Fin l, q ≤ a ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i a = k) ↔
      ∃ b : Fin (l + 1), b ≠ i ∧ i.succAbove q ≤ b ∧ u b = k := by
  constructor
  · rintro ⟨a, ha, hu⟩
    exact ⟨i.succAbove a, Fin.succAbove_ne i a, (Fin.strictMono_succAbove i).monotone ha, hu⟩
  · rintro ⟨b, hbi, hb, hu⟩
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hbi
    refine ⟨a, ?_, ?_⟩
    · apply (Fin.strictMono_succAbove i).le_iff_le.mp
      rwa [ha]
    · simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_apply, ha] using hu

private lemma excluded_occurrence_swap {n l : ℕ} (u : Fin l → Fin n) (i j : Fin l)
    (hij : i ≠ j) (hu : u i = u j) (P : Fin l → Prop) (hP : P i ↔ P j) (k : Fin n) :
    (∃ a, a ≠ i ∧ P a ∧ u a = k) ↔ (∃ a, a ≠ j ∧ P a ∧ u a = k) := by
  constructor
  · rintro ⟨a, ha, hp, hua⟩
    by_cases haj : a = j
    · subst a
      exact ⟨i, hij, hP.mpr hp, hu.trans hua⟩
    · exact ⟨a, haj, hp, hua⟩
  · rintro ⟨a, ha, hp, hua⟩
    by_cases hai : a = i
    · subst a
      exact ⟨j, hij.symm, hP.mp hp, hu.symm.trans hua⟩
    · exact ⟨a, hai, hp, hua⟩

/-- 概要：切断点以外の同じ側の二位置は左右所属が同じ（BF §2.2.7）。
方針：共通の側に分け、切断点との一致を排除する。
規約：切断点自身を交換位置に含めない。
使われ方：削除位置を交換しても各側の色の出現が変わらないことを示す。 -/
lemma sameCutSide_membership {l : ℕ} (p i j : Fin l) (hi : i ≠ p) (hj : j ≠ p)
    (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide p i j) : (i ≤ p ↔ j ≤ p) ∧ (p ≤ i ↔ p ≤ j) := by
  rcases hs with hs | hs
  · have hi' : ¬ p ≤ i := fun h => hi (le_antisymm hs.1 h)
    have hj' : ¬ p ≤ j := fun h => hj (le_antisymm hs.2 h)
    simp [hs.1, hs.2, hi', hj']
  · have hi' : ¬ i ≤ p := fun h => hi (le_antisymm h hs.1)
    have hj' : ¬ j ≤ p := fun h => hj (le_antisymm h hs.2)
    simp [hs.1, hs.2, hi', hj']

/-- 概要：同色・同側の二削除で各色の全出力頂点集合は一致（BF §2.2.7）。
方針：左右の出現の削除位置以外での特徴付けへ、除外位置の交換を適用する。
規約：両方の削除後の切断点が同じ元の切断点へ戻ることを要求する。
使われ方：余分な削除項の交換対の全出力一致。 -/
lemma edgeOutputVertices_swap_deletion {n l : ℕ} (u : Fin (l + 1) → Fin n)
    (i j : Fin (l + 1)) (q q' : Fin l) (hij : i ≠ j) (hu : u i = u j)
    (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.SameCutSide (i.succAbove q) i j) (hq : j.succAbove q' = i.succAbove q)
    (k : Fin n) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u i) q k = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u j) q' k := by
  have hjp : j ≠ i.succAbove q := by rw [← hq]; exact Fin.ne_succAbove j q'
  have hp := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sameCutSide_membership _ i j (Fin.ne_succAbove i q) hjp hs
  apply Finset.ext
  intro b
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_mem_iff, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_mem_iff,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_left_occurrence_excluding, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_right_occurrence_excluding,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_left_occurrence_excluding, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.erase_right_occurrence_excluding]
  simp only [hq]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.excluded_occurrence_swap u i j hij hu (fun a => a ≤ i.succAbove q) hp.1 k,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.excluded_occurrence_swap u i j hij hu (fun a => i.succAbove q ≤ a) hp.2 k]

/-- 概要：固定点なし交換対の各出力頂点集合は厳密に一致（BF §2.2.7）。
方針：削除位置と障害位置の同色・同側の条件を使う。
規約：元切断は退化していてよい。
使われ方：交換対の符号を除いた切断値の一致。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut.swap_output {n l : ℕ} {u : Fin (l + 1) → Fin n}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u) (k : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u c.deleted) c.pivot k =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u c.swap.deleted) c.swap.pivot k :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutputVertices_swap_deletion u c.deleted c.defect c.pivot c.partnerPosition
    c.defect_spec.1.symm c.defect_spec.2.1.symm c.defect_spec.2.2 c.partnerPosition_spec.1 k

/-- 概要：余分な削除切断の実際の削除基底語（BF §2.2.7）。
方針：障害位置の同色出現から全射性、非零切断から非退化性を得る。
規約：元の語の次数 d+1 から次数 d へ移る。
使われ方：交換対を χ の実際の削除基底で計算する。 -/
def residualCutBasisWord {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u.val) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d :=
  ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase u.val c.deleted,
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase_surjective_iff u.val u.surjective c.deleted).mpr
      ⟨c.defect, c.defect_spec.1, c.defect_spec.2.1⟩,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.nondegenerate_of_edgeNondegenerate c.nondegenerate⟩

/-- 概要：交換対の実際の削除語の全出力族は一致（BF §2.2.7）。
方針：各色の頂点集合の一致を面の部分型の一致へ移す。
規約：両方とも非退化な全射基底語。
使われ方：実際の区間テンソルの切断値を比較する。 -/
lemma residualCut_output_family {n d : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1))
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residualCutBasisWord u c) c.pivot =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residualCutBasisWord u c.swap) c.swap.pivot := by
  funext k
  apply Subtype.ext
  exact c.swap_output k

/-- 概要：交換対の実際の切断テンソルの値は符号を除いて一致（BF §2.2.7）。
方針：全出力族の一致を同じ指定次数の反復テンソルへ渡す。
規約：元の語次数 d+1 の削除後の辺切断の次数は d+1。
使われ方：削除係数と切断符号の反対性から二項を相殺する。 -/
lemma residualCut_tensor_eq (A : Type u) [CommRing A] {n d : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n (d + 1)) (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.NonpivotResidualCut u.val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n (d + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residualCutBasisWord u c) c.pivot)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ c.nondegenerate) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorOfDegree A n (d + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residualCutBasisWord u c.swap) c.swap.pivot)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ c.swap.nondegenerate) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.tensorVectorAt_congr A n _ _ (-((d + 1 : ℕ) : ℤ))
    (congrArg (fun r : ℕ => -(r : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ c.nondegenerate))
    (congrArg (fun r : ℕ => -(r : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeOutput_tupleDegree _ _ c.swap.nondegenerate))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.residualCut_output_family u c)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

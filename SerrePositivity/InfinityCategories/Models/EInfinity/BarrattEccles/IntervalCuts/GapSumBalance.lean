module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.PivotResidualEquivalences

/-!
模型。文献の定義との比較は後で
# 隙間の両隣の非零切断と退化切断の有限和の釣り合い

概要：Berger–Fresse §2.2.7 の削除和と切断点境界和を隙間ごとの補集合として比較する。
方針：全隙間和を左右から数え、非零辺切断と残りの退化切断へ分割する。
規約：先頭前と末尾後の値が零である任意の可換加法群値を扱う。
使われ方：正次数の切断点障害全削除和と切断点色全因子境界和の一致。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open scoped _root_.BigOperators

private lemma sum_ite_subtype {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] (F : α → M) :
    (∑ a, if P a then F a else 0) = ∑ a : {a // P a}, F a.val := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun _ => by simp) F

private lemma sum_partition {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] (hpq : ∀ a, P a → Q a)
    (F : α → M) :
    (∑ a, if Q a then F a else 0) =
      (∑ a : {a // P a}, F a.val) + ∑ a : {a // Q a ∧ ¬ P a}, F a.val := by
  classical
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_ite_subtype P F, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_ite_subtype (fun a => Q a ∧ ¬ P a) F,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : P a
  · simp only [hp, hpq a hp, and_false, not_true_eq_false, ite_true, ite_false, add_zero]
  · by_cases hq : Q a <;> simp only [hp, hq, and_self, not_false_eq_true,
      false_and, ite_true, ite_false, zero_add]

/-- 概要：退化隣接切断の右隙間和−左隙間和は非零辺切断の隙間差和（BF §2.2.7）。
方針：左右からの全隙間和は両端零で一致し、非零辺切断の補集合を取る。
規約：隙間の非退化性を保ち、元の非零辺切断の存在は要求しない。
使われ方：実際の区間テンソル値の全削除和と全因子境界和を比較する。 -/
lemma gap_sum_complement {n l : ℕ} (u : Fin l → Fin n) {M : Type*} [AddCommGroup M]
    (F : Fin (l + 1) → M) (hfirst : F 0 = 0) (hlast : F (Fin.last l) = 0) :
    ((∑ p : {p : Fin l // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.succ ∧ ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p}, F p.val.succ) -
      ∑ p : {p : Fin l // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.castSucc ∧ ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p},
        F p.val.castSucc) =
      ∑ p : {p : Fin l // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u p}, (F p.val.castSucc - F p.val.succ) := by
  classical
  let f (q : Fin (l + 1)) := if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u q then F q else 0
  have hf : f 0 = 0 := by simp only [f, hfirst, ite_self]
  have hl : f (Fin.last l) = 0 := by simp only [f, hlast, ite_self]
  have hbal : (∑ p : Fin l, f p.castSucc) = ∑ p : Fin l, f p.succ := by
    have h := (Fin.sum_univ_castSucc f).symm.trans (Fin.sum_univ_succ f)
    simpa only [hf, hl, add_zero, zero_add] using h
  have hb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_partition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u) (fun p => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.castSucc)
    (fun _ h => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapNondegenerate_before h) (fun p => F p.castSucc)
  have ha := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.sum_partition (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.EdgeNondegenerate u) (fun p => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GapNondegenerate u p.succ)
    (fun _ h => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.gapNondegenerate_after h) (fun p => F p.succ)
  rw [Finset.sum_sub_distrib]
  apply sub_eq_sub_iff_add_eq_add.mpr
  have he := hb.symm.trans (hbal.trans ha)
  exact (add_comm _ _).trans he.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

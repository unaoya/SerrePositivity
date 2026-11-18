module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.GeneralDeletionCaesuras
public import Mathlib.Data.Fintype.EquivFin

/-!
模型。文献の定義との比較は後で
# 次数一の語の二つの非零削除係数

概要：Berger–Fresse §1.2.3 の次数一の全射語では区切りが一つで、非零削除係数は +1 と −1。
方針：区切り部分型の濃度一から唯一の前出現を取り、後出現の最終性と他位置の単独性を使う。
規約：元の辺切断の存在は仮定しない。
使われ方：次数一から零次数への頂点成分の微分保存。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：次数一の語の区切りは一意に存在する（BF §1.2.2）。
方針：区切り部分型の濃度が一であることを使う。
規約：全 arity を扱う。
使われ方：唯一の反復色の前出現を選ぶ。 -/
lemma degreeOne_caesura_existsUnique {n : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 1) :
    ∃! a, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val a := by
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.card_caesuras_basisWord u)
  refine ⟨a.val, a.property, ?_⟩
  intro b hb
  exact congrArg Subtype.val (ha ⟨b, hb⟩)

/-- 概要：前後いずれにも同色がなければ削除係数は零（BF §1.2.3）。
方針：区切りと先行同色集合の非空性をともに排除する。
規約：任意の有限語に成立する。
使われ方：唯一色の削除項を微分の和から除く。 -/
lemma deletionCoefficient_eq_zero_of_unique {n l : ℕ} (u : Fin l → Fin n) (i : Fin l)
    (h : ∀ j, u j = u i → j = i) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u i = 0 := by
  have hc : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u i := by
    rintro ⟨j, hij, hu⟩
    exact (ne_of_gt hij) (h j hu)
  have hp : ¬ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences u i).Nonempty := by
    rintro ⟨j, hj⟩
    have hj' := (Finset.mem_filter.mp hj).2
    exact (ne_of_lt hj'.1) (h j hj'.2)
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient, ite_eq_right hc, dite_eq_right hp]

/-- 概要：次数一の語の非零削除係数は反復色の前後二位置で +1・−1（BF §1.2.3）。
方針：唯一の区切りの順位零を計算し、後出現の最終性と他の同色出現の不在を使う。
規約：他の全位置の削除係数は零。
使われ方：頂点成分へ送った削除微分の二項相殺。 -/
lemma degreeOne_deletion_pair {n : ℕ} (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n 1) :
    ∃ a b, a < b ∧ u.val a = u.val b ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u.val a = 1 ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u.val b = -1 ∧
        ∀ i, i ≠ a → i ≠ b → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u.val i = 0 := by
  obtain ⟨a, ha, hall⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.degreeOne_caesura_existsUnique u
  obtain ⟨b, hab, hba⟩ := ha
  have ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val a := ⟨b, hab, hba⟩
  have hr : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank u.val a = 0 := by
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraRank
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact (ne_of_lt hj'.1) (hall j hj'.2)
  have hca : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u.val a = 1 := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient_of_caesura u.val a ha, hr, pow_zero]
  have hbn : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Caesura u.val b := fun hb => (ne_of_gt hab) (hall b hb)
  have hgap : ∀ j, a < j → j < b → u.val j ≠ u.val b := by
    intro j haj hjb huj
    exact (ne_of_gt haj) (hall j ⟨b, hjb, huj.symm⟩)
  have hcb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient u.val b = -1 := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.deletionCoefficient_final_gap u.val a b hab hba.symm hbn hgap, hca]
  refine ⟨a, b, hab, hba.symm, hca, hcb, ?_⟩
  intro i hia hib
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.deletionCoefficient_eq_zero_of_unique u.val i
  intro j huj
  by_contra hji
  rcases lt_or_gt_of_ne hji with hji | hij
  · have hja := hall j ⟨i, hji, huj.symm⟩
    have huia : u.val i = u.val a := huj.symm.trans (congrArg u.val hja)
    rcases lt_or_gt_of_ne hib with hib | hbi
    · exact hia (hall i ⟨b, hib, hba.trans huia.symm⟩)
    · exact (ne_of_gt hab) (hall b ⟨i, hbi, huia.trans hba.symm⟩)
  · have hia' := hall i ⟨j, hij, huj⟩
    exact hia hia'

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

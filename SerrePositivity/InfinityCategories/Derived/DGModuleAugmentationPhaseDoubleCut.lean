module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationCorrectionDifferential
/-!
概要：単調な切断支持において、二重切断の同相部分を相殺し異相部分を残す。
方針：同じ順序付き点対の和に移し、実次数符号と支持の単調性を使う。
規約：値には任意の可換群を許す。使われ方：候補補正の同じ三重合成の二次相殺。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.InfinityCategories
open DGNerve
/-- 単調な支持の二重切断和は、支持外から支持内への切断対の寄与に等しい。 -/
lemma dgModuleAugmentationPhase_double_cut_cancel {α : Type*} [LinearOrder α]
    {M : Type*} [AddCommGroup M] (I K : Finset α) (hKI : K ⊆ I)
    (p : α → Prop) [DecidablePred p]
    (hmono : ∀ j ∈ K, ∀ k ∈ K, j < k → p j → p k) (f : α → α → M) :
    (∑ j ∈ K, Index.sign I j • ∑ k ∈ K.filter (j < ·),
      Index.sign (I.filter (j ≤ ·)) k • (if p j then f j k else 0)) +
    (∑ k ∈ K, Index.sign I k •
      ((2 - ((I.filter (k ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ K.filter (· < k), Index.sign (I.filter (· ≤ k)) j •
        (if p k then f j k else 0))) =
    ∑ k ∈ K, Index.sign I k •
      ((2 - ((I.filter (k ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ K.filter (· < k), Index.sign (I.filter (· ≤ k)) j •
        (if p k ∧ ¬ p j then f j k else 0)) := by
  simp only [Finset.sum_filter, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjk : j < k
  · simp only [ite_eq_left hjk]
    by_cases hpj : p j
    · have hpk := hmono j hj k hk hjk hpj
      have hn : ¬ (p k ∧ ¬ p j) := by
        simp only [hpj, not_true_eq_false, and_false, not_false_eq_true]
      simp only [ite_eq_left hpj, ite_eq_left hpk, ite_eq_right hn,
        smul_smul, ← mul_assoc]
      rw [Index.sign_double_cut I (hKI hk) hjk]
      simp [Units.smul_def]
    · by_cases hpk : p k <;> simp [hpj, hpk]
  · simp only [ite_eq_right hjk, add_zero]
end SerrePositivity.InfinityCategories

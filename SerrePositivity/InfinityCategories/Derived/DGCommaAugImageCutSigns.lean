module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugQuadraticCancellation
/-!
概要：中央比較三重合成の二重切断に現れる、相付き次数符号の相殺を証明する。
方針：同じ点対で切断順序の符号を比較し、支持の単調性を使う。
規約：同じ実係数を保持する。使われ方：候補の全二次境界との比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
/-- 中央比較三重合成の二つの切断係数は、追加の右次数符号も含めて相殺する。 -/
lemma dgCommaAugmentationImage_double_cut_cancel {α : Type*} [LinearOrder α]
    {M : Type*} [AddCommGroup M] (I : Finset α)
    {j l : α} (hl : l ∈ I) (hjl : j < l) (z : M) :
    Index.sign I j • (Index.sign (I.filter (j ≤ ·)) l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow • z)) +
      Index.sign I l • (Index.sign (I.filter (· ≤ l)) j • z) = 0 := by
  let q := 2 - ((I.filter (l ≤ ·)).card : ℤ)
  have hsq : q.negOnePow * q.negOnePow = 1 := by
    rw [← Int.negOnePow_add, show q + q = 2 * q by omega, Int.negOnePow_two_mul]
  have hc : Index.sign I j * Index.sign (I.filter (j ≤ ·)) l * q.negOnePow =
      -(Index.sign I l * Index.sign (I.filter (· ≤ l)) j) := by
    rw [Index.sign_double_cut I hl hjl]
    calc
      -(Index.sign I l * q.negOnePow * Index.sign (I.filter (· ≤ l)) j) * q.negOnePow =
          -(Index.sign I l * Index.sign (I.filter (· ≤ l)) j *
            (q.negOnePow * q.negOnePow)) := by
        rw [neg_mul]
        congr 1
        ac_rfl
      _ = _ := by rw [hsq, mul_one]
  change Index.sign I j • (Index.sign (I.filter (j ≤ ·)) l • (q.negOnePow • z)) + _ = 0
  simp only [smul_smul]
  rw [← mul_assoc, hc]
  simp [Units.smul_def]
/-- 単調な切断支持における、中央比較三重合成の全符号和の相殺。 -/
lemma dgCommaAugmentationImage_phase_double_cut_cancel {α : Type*} [LinearOrder α]
    {M : Type*} [AddCommGroup M] (I K : Finset α) (hKI : K ⊆ I)
    (p : α → Prop) [DecidablePred p]
    (hmono : ∀ j ∈ K, ∀ l ∈ K, j < l → p j → p l) (f : α → α → M) :
    (∑ j ∈ K, Index.sign I j • ∑ l ∈ K.filter (j < ·),
      Index.sign (I.filter (j ≤ ·)) l •
        ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        (if p j then f j l else 0))) +
    (∑ l ∈ K, Index.sign I l • ∑ j ∈ K.filter (· < l),
      Index.sign (I.filter (· ≤ l)) j • (if p l ∧ p j then f j l else 0)) = 0 := by
  simp only [Finset.sum_filter, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro l hl
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hjl : j < l
  · simp only [ite_eq_left hjl]
    by_cases hpj : p j
    · have hpl := hmono j hj l hl hjl hpj
      simpa only [ite_eq_left hpj, ite_eq_left (show p l ∧ p j from ⟨hpl, hpj⟩)] using
        dgCommaAugmentationImage_double_cut_cancel I (hKI hl) hjl (f j l)
    · simp [hpj]
  · simp only [ite_eq_right hjl, add_zero]
end SerrePositivity.InfinityCategories

module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugImageCutSigns
/-!
概要：実候補の左補正の後合成を、中央比較三重合成の同じ有限和へ接続する。
方針：同じ左右区間の切断和に展開し、実三重合成の順序同定と相付き符号を使う。
規約：同じ実係数を保持する。使われ方：候補の全二次境界との比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
/-- 候補の同じ左補正に元の右入力像を後合成する実係数。 -/
def dgCommaAugmentationImageCorrection (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (l : Fin (n + 1)) :
    GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 then
    compose R (x := (s.obj a).replacement) (y := F.obj (s.obj l).source)
      (z := F.obj (s.obj b).source) (n := k + 1)
      ((dgFunctorCommaImageHomMap R C E F (s.obj l) (s.obj b)).f _
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (dgCommaAugmentationPrismCorrection R C E F s β (I.filter (· ≤ l)) a l
        (2 - ((I.filter (· ≤ l)).card : ℤ))) h
  else 0
/-- 左補正の後合成は、同じ中央比較三重合成の切断和。 -/
lemma dgCommaAugmentationImageCorrection_expansion
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (l : Fin (n + 1)) (hl : l ∈ I) (hlb : l < b) :
    dgCommaAugmentationImageCorrection R C E F s β I a b k l =
    ∑ j ∈ ((Index.interior I a b).filter (· < l)).filter (β · = 1),
      Index.sign (I.filter (· ≤ l)) j •
        dgCommaAugmentationNestedImageLeft R C E F s I a b k j l := by
  have hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 := by
    have := Index.split_card hl
    omega
  rw [dgCommaAugmentationImageCorrection, dite_eq_left hsum]
  simp only [dgCommaAugmentationPrismCorrection, compose_sum_right, compose_units_smul_right,
    dgCommaAugmentationCutPoints_eq_filter_interior, Index.interior_left_cut I a b l hlb]
  apply Finset.sum_congr rfl
  intro j _
  rw [dgCommaAugmentationNestedImageLeft, dite_eq_left hsum]
/-- 中央比較三重合成の全相付き和と同じ左補正の後合成和は相殺する。 -/
lemma dgCommaAugmentationImageCorrection_sum_cancel
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I j •
      ∑ l ∈ (Index.interior I a b).filter (j < ·), Index.sign (I.filter (j ≤ ·)) l •
        ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
          dgCommaAugmentationNestedImageRight R C E F s I a b k j l)) +
    (∑ l ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I l •
      dgCommaAugmentationImageCorrection R C E F s β I a b k l) = 0 := by
  have hr :
      (∑ j ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I j •
        ∑ l ∈ (Index.interior I a b).filter (j < ·), Index.sign (I.filter (j ≤ ·)) l •
          ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
            dgCommaAugmentationNestedImageRight R C E F s I a b k j l)) =
      (∑ j ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I j •
        ∑ l ∈ (Index.interior I a b).filter (j < ·), Index.sign (I.filter (j ≤ ·)) l •
          ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
            dgCommaAugmentationNestedImageLeft R C E F s I a b k j l)) := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [dgCommaAugmentationNestedImageRight_eq_left R C E F s I a b k hk j l
      (Finset.mem_filter.mp hj).1
      (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).1 (Finset.mem_filter.mp hl).2]
  have hl :
      (∑ l ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I l •
        dgCommaAugmentationImageCorrection R C E F s β I a b k l) =
      ∑ l ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I l •
        ∑ j ∈ ((Index.interior I a b).filter (· < l)).filter (β · = 1),
          Index.sign (I.filter (· ≤ l)) j •
            dgCommaAugmentationNestedImageLeft R C E F s I a b k j l := by
    apply Finset.sum_congr rfl
    intro l hl
    have hm := Finset.mem_filter.mp hl
    rw [dgCommaAugmentationImageCorrection_expansion R C E F s β I a b k hk
      l hm.1 hm.2.2.1]
  have hm : ∀ j ∈ Index.interior I a b, ∀ l ∈ Index.interior I a b,
      j < l → β j = 1 → β l = 1 := by
    intro j _ l _ hjl hp
    have h := β.monotone hjl.le
    rw [hp] at h
    apply Fin.ext
    have := (β l).isLt
    change (β l).val = 1
    change 1 ≤ (β l).val at h
    omega
  rw [hr, hl]
  have hc := dgCommaAugmentationImage_phase_double_cut_cancel I (Index.interior I a b)
    (Finset.filter_subset _ _) (fun j ↦ β j = 1) hm
    (fun j l ↦ dgCommaAugmentationNestedImageLeft R C E F s I a b k j l)
  simpa only [dgCommaAugmentationCutPoints_eq_filter_interior, Finset.sum_filter,
    ite_and, smul_ite, smul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero] using hc
end SerrePositivity.InfinityCategories

module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationImageCorrection
/-!
概要：実候補の右補正と左入力像の合成を、右比較三重合成の同じ切断和へ接続する。
方針：元の右切断補正の有限和を合成の線形性で展開する。
規約：同じ実係数を保持する。使われ方：候補の全二次境界との比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  {n : ℕ} (s : SimplexData R (DGModuleFunctorResolutionObject R C E F) n)
/-- 候補の同じ右補正に元の左入力像を前合成する実係数。 -/
def dgModuleAugmentationSuffixCorrection (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1)) :
    GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 then
    compose R (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgModuleAugmentationPrismCorrection R C E F s β (I.filter (j ≤ ·)) j b
        (2 - ((I.filter (j ≤ ·)).card : ℤ)))
      (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
        (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)))) h
  else 0
/-- 右補正の前合成は、同じ右比較三重合成の切断和。 -/
lemma dgModuleAugmentationSuffixCorrection_expansion
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) :
    dgModuleAugmentationSuffixCorrection R C E F s β I a b k j =
    ∑ l ∈ ((Index.interior I a b).filter (j < ·)).filter (β · = 1),
      Index.sign (I.filter (j ≤ ·)) l •
        dgModuleAugmentationNestedHomotopyRight R C E F s I a b k j l := by
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := Index.split_card hj
    omega
  rw [dgModuleAugmentationSuffixCorrection, dite_eq_left hsum]
  simp only [dgModuleAugmentationPrismCorrection,
    dgModuleAugmentationCutPoints_eq_filter_interior, Index.interior_right_cut I a b j haj]
  trans ∑ l ∈ ((Index.interior I a b).filter (j < ·)).filter (β · = 1),
    compose R
      (Index.sign (I.filter (j ≤ ·)) l •
        dgModuleAugmentationHomotopyCut R C E F s (I.filter (j ≤ ·)) j b
          (2 - ((I.filter (j ≤ ·)).card : ℤ)) l)
      (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
        (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)))) hsum
  · exact compose_sum_left _ _ _ hsum
  · apply Finset.sum_congr rfl
    intro l _
    rw [dgModuleAugmentationNestedHomotopyRight, dite_eq_left hsum]
    exact compose_units_smul_left _ _ _ hsum
/-- 異相の右比較三重合成和は、同じ実右補正の前合成和と相殺する。 -/
lemma dgModuleAugmentationSuffixCorrection_sum_cancel
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
      dgModuleAugmentationSuffixCorrection R C E F s β I a b k j) +
    (∑ l ∈ Index.interior I a b, Index.sign I l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ (Index.interior I a b).filter (· < l), Index.sign (I.filter (· ≤ l)) j •
        (if β l = 1 ∧ ¬ β j = 1 then
          dgModuleAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0))) = 0 := by
  have he :
      (∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
        dgModuleAugmentationSuffixCorrection R C E F s β I a b k j) =
      ∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
        ∑ l ∈ ((Index.interior I a b).filter (j < ·)).filter (β · = 1),
          Index.sign (I.filter (j ≤ ·)) l •
            dgModuleAugmentationNestedHomotopyRight R C E F s I a b k j l := by
    apply Finset.sum_congr rfl
    intro j hj
    have hm := Finset.mem_filter.mp (Finset.mem_filter.mp hj).1
    rw [dgModuleAugmentationSuffixCorrection_expansion R C E F s β I a b k hk
      j hm.1 hm.2.1]
  rw [he]
  have hr :
      (∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
        ∑ l ∈ ((Index.interior I a b).filter (j < ·)).filter (β · = 1),
          Index.sign (I.filter (j ≤ ·)) l •
            dgModuleAugmentationNestedHomotopyRight R C E F s I a b k j l) =
      ∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
        ∑ l ∈ ((Index.interior I a b).filter (j < ·)).filter (β · = 1),
          Index.sign (I.filter (j ≤ ·)) l •
            dgModuleAugmentationNestedHomotopyLeft R C E F s I a b k j l := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [dgModuleAugmentationNestedHomotopyRight_eq_left R C E F s I a b k hk j l
      (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).1).1
      (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2]
  rw [hr]
  have hc := Index.sum_double_cut_cancel I (Index.interior I a b) (Finset.filter_subset _ _)
    (fun j l ↦ if β l = 1 ∧ ¬ β j = 1 then
      dgModuleAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0)
  have hf :
      (∑ j ∈ Index.interior I a b, Index.sign I j •
        ∑ l ∈ (Index.interior I a b).filter (j < ·), Index.sign (I.filter (j ≤ ·)) l •
          (if β l = 1 ∧ ¬ β j = 1 then
            dgModuleAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0)) =
      ∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
        ∑ l ∈ ((Index.interior I a b).filter (j < ·)).filter (β · = 1),
          Index.sign (I.filter (j ≤ ·)) l •
            dgModuleAugmentationNestedHomotopyLeft R C E F s I a b k j l := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : β j = 1
    · simp [hj]
    · simp [hj, Finset.sum_filter]
  rw [← hf]
  exact hc
end SerrePositivity.InfinityCategories

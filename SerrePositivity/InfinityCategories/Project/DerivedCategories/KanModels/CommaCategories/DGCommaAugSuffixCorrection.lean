module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugImageCorrection
/-!
概要：実候補の右補正と左入力像の合成を、右比較三重合成の同じ切断和へ接続する。
方針：元の右切断補正の有限和を合成の線形性で展開する。
規約：同じ実係数を保持する。使われ方：候補の全二次境界との比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
/-- 候補の同じ右補正に元の左入力像を前合成する実係数。 -/
def dgCommaAugmentationSuffixCorrection (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 then
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement) (y := (s.obj j).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCorrection R C E F s β (I.filter (j ≤ ·)) j b
        (2 - ((I.filter (j ≤ ·)).card : ℤ)))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
        (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)))) h
  else 0
/-- 右補正の前合成は、同じ右比較三重合成の切断和。 -/
lemma dgCommaAugmentationSuffixCorrection_expansion
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) :
    dgCommaAugmentationSuffixCorrection R C E F s β I a b k j =
    ∑ l ∈ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·)).filter (β · = 1),
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyRight R C E F s I a b k j l := by
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  rw [dgCommaAugmentationSuffixCorrection, dite_eq_left hsum]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationPrismCorrection,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints_eq_filter_interior, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior_right_cut I a b j haj]
  trans ∑ l ∈ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·)).filter (β · = 1),
    _root_.SerrePositivity.DifferentialGraded.compose R
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyCut R C E F s (I.filter (j ≤ ·)) j b
          (2 - ((I.filter (j ≤ ·)).card : ℤ)) l)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
        (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)))) hsum
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_left _ _ _ hsum
  · apply Finset.sum_congr rfl
    intro l _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyRight, dite_eq_left hsum]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left _ _ _ hsum
/-- 異相の右比較三重合成和は、同じ実右補正の前合成和と相殺する。 -/
lemma dgCommaAugmentationSuffixCorrection_sum_cancel
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (β · ≠ 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      dgCommaAugmentationSuffixCorrection R C E F s β I a b k j) +
    (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
        (if β l = 1 ∧ ¬ β j = 1 then
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0))) = 0 := by
  have he :
      (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (β · ≠ 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        dgCommaAugmentationSuffixCorrection R C E F s β I a b k j) =
      ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (β · ≠ 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        ∑ l ∈ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·)).filter (β · = 1),
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyRight R C E F s I a b k j l := by
    apply Finset.sum_congr rfl
    intro j hj
    have hm := Finset.mem_filter.mp (Finset.mem_filter.mp hj).1
    rw [dgCommaAugmentationSuffixCorrection_expansion R C E F s β I a b k hk
      j hm.1 hm.2.1]
  rw [he]
  have hr :
      (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (β · ≠ 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        ∑ l ∈ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·)).filter (β · = 1),
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyRight R C E F s I a b k j l) =
      ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (β · ≠ 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        ∑ l ∈ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·)).filter (β · = 1),
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyRight_eq_left R C E F s I a b k hk j l
      (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).1).1
      (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2]
  rw [hr]
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.sum_double_cut_cancel I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b) (Finset.filter_subset _ _)
    (fun j l ↦ if β l = 1 ∧ ¬ β j = 1 then
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0)
  have hf :
      (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
          (if β l = 1 ∧ ¬ β j = 1 then
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0)) =
      ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (β · ≠ 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        ∑ l ∈ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·)).filter (β · = 1),
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : β j = 1
    · simp [hj]
    · simp [hj, Finset.sum_filter]
  rw [← hf]
  exact hc
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationQuadraticCancellation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AugmentationCombinatorics
/-!
概要：実候補の左補正の後合成を、中央比較三重合成の同じ有限和へ接続する。
方針：同じ左右区間の切断和に展開し、実三重合成の順序同定と相付き符号を使う。
規約：同じ実係数を保持する。使われ方：候補の全二次境界との比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 候補の同じ左補正に元の右入力像を後合成する実係数。 -/
def dgModuleAugmentationImageCorrection (β : Fin (n + 1) →o Fin 2)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (l : Fin (n + 1)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 then
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := F.obj (s.obj l).source)
      (z := F.obj (s.obj b).source) (n := k + 1)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F (s.obj l) (s.obj b)).f _
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCorrection R C E F s β (I.filter (· ≤ l)) a l
        (2 - ((I.filter (· ≤ l)).card : ℤ))) h
  else 0
/-- 左補正の後合成は、同じ中央比較三重合成の切断和。 -/
lemma dgModuleAugmentationImageCorrection_expansion
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (l : Fin (n + 1)) (hl : l ∈ I) (hlb : l < b) :
    dgModuleAugmentationImageCorrection R C E F s β I a b k l =
    ∑ j ∈ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l)).filter (β · = 1),
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedImageLeft R C E F s I a b k j l := by
  have hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hl
    omega
  rw [dgModuleAugmentationImageCorrection, dite_eq_left hsum]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCorrection, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints_eq_filter_interior, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior_left_cut I a b l hlb]
  apply Finset.sum_congr rfl
  intro j _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedImageLeft, dite_eq_left hsum]
/-- 中央比較三重合成の全相付き和と同じ左補正の後合成和は相殺する。 -/
lemma dgModuleAugmentationImageCorrection_sum_cancel
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
        ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedImageRight R C E F s I a b k j l)) +
    (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      dgModuleAugmentationImageCorrection R C E F s β I a b k l) = 0 := by
  have hr :
      (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
          ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedImageRight R C E F s I a b k j l)) =
      (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
          ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedImageLeft R C E F s I a b k j l)) := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedImageRight_eq_left R C E F s I a b k hk j l
      (Finset.mem_filter.mp hj).1
      (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).1 (Finset.mem_filter.mp hl).2]
  have hl :
      (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
        dgModuleAugmentationImageCorrection R C E F s β I a b k l) =
      ∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
        ∑ j ∈ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l)).filter (β · = 1),
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedImageLeft R C E F s I a b k j l := by
    apply Finset.sum_congr rfl
    intro l hl
    have hm := Finset.mem_filter.mp hl
    rw [dgModuleAugmentationImageCorrection_expansion R C E F s β I a b k hk
      l hm.1 hm.2.2.1]
  have hm : ∀ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, ∀ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b,
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
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationImage_phase_double_cut_cancel I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b)
    (Finset.filter_subset _ _) (fun j ↦ β j = 1) hm
    (fun j l ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedImageLeft R C E F s I a b k j l)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints_eq_filter_interior, Finset.sum_filter,
    ite_and, smul_ite, smul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero] using hc
end SerrePositivity.InfinityCategories.Project.DerivedCategories

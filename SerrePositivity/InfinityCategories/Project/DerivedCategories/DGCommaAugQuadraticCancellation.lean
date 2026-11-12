module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugNestedPhaseCancellation
/-!
概要：同じ実二次切断境界の全相付き和から、右比較三重合成の同相部分を消す。
方針：実二次切断展開を総和し、同じ実係数を持つ相付き二重切断相殺を適用する。
規約：中央比較補正と異相右比較補正を明示して残す。
使われ方：候補の全二次境界との最終比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
/-- 全実二次切断和は、中央比較三重合成と異相の右比較三重合成の二和。 -/
lemma dgCommaAugmentationCutQuadraticBoundary_sum_reduction
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationCutQuadraticBoundary R C E F s I a b k j) =
    (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
        ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedImageRight R C E F s I a b k j l)) +
    (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
        (if β l = 1 ∧ ¬ β j = 1 then
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0))) := by
  let U := ∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
    ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedImageRight R C E F s I a b k j l)
  let V := ∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
    ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyRight R C E F s I a b k j l
  let W := ∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
    ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
    ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l)
  have hd :
      (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationCutQuadraticBoundary R C E F s I a b k j) = U + V + W := by
    dsimp only [U, V, W]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hm := Finset.mem_filter.mp hj
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationCutQuadraticBoundary_expansion R C E F s I a b k hk
      j hm.1 hm.2.1 hm.2.2.1]
    simp only [smul_add, Finset.sum_add_distrib]
  have hc : V + W =
      ∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
        ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
          (if β l = 1 ∧ ¬ β j = 1 then
            _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0)) := by
    dsimp only [V, W]
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints_eq_filter_interior, Finset.sum_filter,
      smul_ite, smul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero] using
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopy_phase_cancel R C E F s β I a b k hk
  rw [hd, add_assoc, hc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories

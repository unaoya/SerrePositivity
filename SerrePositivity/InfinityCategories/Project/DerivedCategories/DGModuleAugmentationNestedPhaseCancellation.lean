module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationQuadraticCutExpansion
/-!
概要：同じ右比較三重合成の相付き二重切断和で、同相部分を相殺する。
方針：二つの実切断順の同定と相の単調性から、実係数を持つ符号相殺を適用する。
規約：右比較成分の同じ実値を保持する。使われ方：二次境界を候補の右補正へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ右比較三重合成の二重和は、相零から相一へ渡る切断対の寄与に等しい。 -/
lemma dgModuleAugmentationNestedHomotopy_phase_cancel
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
        (if β j = 1 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedHomotopyRight R C E F s I a b k j l
          else 0)) +
    (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
        (if β l = 1 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedHomotopyLeft R C E F s I a b k j l
          else 0))) =
    ∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
        (if β l = 1 ∧ ¬ β j = 1 then
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0)) := by
  have hs :
      (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
          (if β j = 1 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedHomotopyRight R C E F s I a b k j l
            else 0)) =
      (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
        ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
          (if β j = 1 then _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedHomotopyLeft R C E F s I a b k j l
            else 0)) := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    congr 1
    split_ifs
    · exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationNestedHomotopyRight_eq_left R C E F s I a b k hk
        j l (Finset.mem_filter.mp hj).1
        (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).1 (Finset.mem_filter.mp hl).2
    · rfl
  rw [hs]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationPhase_double_cut_cancel I (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b)
    (Finset.filter_subset _ _) (fun j ↦ β j = 1)
  intro j _ l _ hjl hp
  have h := β.monotone hjl.le
  rw [hp] at h
  apply Fin.ext
  have := (β l).isLt
  change (β l).val = 1
  change 1 ≤ (β l).val at h
  omega
end SerrePositivity.InfinityCategories.Project.DerivedCategories

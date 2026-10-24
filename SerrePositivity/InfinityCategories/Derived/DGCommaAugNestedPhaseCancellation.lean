module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugQuadraticCutExpansion
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
/-- 同じ右比較三重合成の二重和は、相零から相一へ渡る切断対の寄与に等しい。 -/
lemma dgCommaAugmentationNestedHomotopy_phase_cancel
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ Index.interior I a b, Index.sign I j •
      ∑ l ∈ (Index.interior I a b).filter (j < ·), Index.sign (I.filter (j ≤ ·)) l •
        (if β j = 1 then dgCommaAugmentationNestedHomotopyRight R C E F s I a b k j l
          else 0)) +
    (∑ l ∈ Index.interior I a b, Index.sign I l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ (Index.interior I a b).filter (· < l), Index.sign (I.filter (· ≤ l)) j •
        (if β l = 1 then dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l
          else 0))) =
    ∑ l ∈ Index.interior I a b, Index.sign I l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ (Index.interior I a b).filter (· < l), Index.sign (I.filter (· ≤ l)) j •
        (if β l = 1 ∧ ¬ β j = 1 then
          dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0)) := by
  have hs :
      (∑ j ∈ Index.interior I a b, Index.sign I j •
        ∑ l ∈ (Index.interior I a b).filter (j < ·), Index.sign (I.filter (j ≤ ·)) l •
          (if β j = 1 then dgCommaAugmentationNestedHomotopyRight R C E F s I a b k j l
            else 0)) =
      (∑ j ∈ Index.interior I a b, Index.sign I j •
        ∑ l ∈ (Index.interior I a b).filter (j < ·), Index.sign (I.filter (j ≤ ·)) l •
          (if β j = 1 then dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l
            else 0)) := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    congr 1
    split_ifs
    · exact dgCommaAugmentationNestedHomotopyRight_eq_left R C E F s I a b k hk
        j l (Finset.mem_filter.mp hj).1
        (Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).1 (Finset.mem_filter.mp hl).2
    · rfl
  rw [hs]
  apply dgModuleAugmentationPhase_double_cut_cancel I (Index.interior I a b)
    (Finset.filter_subset _ _) (fun j ↦ β j = 1)
  intro j _ l _ hjl hp
  have h := β.monotone hjl.le
  rw [hp] at h
  apply Fin.ext
  have := (β l).isLt
  change (β l).val = 1
  change 1 ≤ (β l).val at h
  omega
end SerrePositivity.InfinityCategories

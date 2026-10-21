module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugSuffixCorrection
/-!
概要：同じ実二次切断和を、候補の左補正の後合成と右補正の前合成へ移す。
方針：実三重合成の相付き還元と、左右それぞれの実補正との総和相殺を結合する。
規約：二次切断和全体を計算し、仮定として要求しない。
使われ方：実候補の微分を候補の全二次境界へ接続する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
/-- 同じ全実二次切断和は、候補の左右補正の同じ合成和と相殺する。 -/
lemma dgCommaAugmentationCutQuadraticBoundary_corrections_cancel
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I j •
      dgCommaAugmentationCutQuadraticBoundary R C E F s I a b k j) +
    (∑ l ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I l •
      dgCommaAugmentationImageCorrection R C E F s β I a b k l) +
    (∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
      dgCommaAugmentationSuffixCorrection R C E F s β I a b k j) = 0 := by
  let U := ∑ j ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I j •
    ∑ l ∈ (Index.interior I a b).filter (j < ·), Index.sign (I.filter (j ≤ ·)) l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        dgCommaAugmentationNestedImageRight R C E F s I a b k j l)
  let V := ∑ l ∈ Index.interior I a b, Index.sign I l •
    ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
    ∑ j ∈ (Index.interior I a b).filter (· < l), Index.sign (I.filter (· ≤ l)) j •
      (if β l = 1 ∧ ¬ β j = 1 then
        dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0))
  let L := ∑ l ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I l •
    dgCommaAugmentationImageCorrection R C E F s β I a b k l
  let T := ∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
    dgCommaAugmentationSuffixCorrection R C E F s β I a b k j
  have hq :
      (∑ j ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I j •
        dgCommaAugmentationCutQuadraticBoundary R C E F s I a b k j) = U + V :=
    dgCommaAugmentationCutQuadraticBoundary_sum_reduction R C E F s β I a b k hk
  have hl : U + L = 0 := dgCommaAugmentationImageCorrection_sum_cancel R C E F s β I a b k hk
  have hr : T + V = 0 := dgCommaAugmentationSuffixCorrection_sum_cancel R C E F s β I a b k hk
  change _ + L + T = 0
  rw [hq]
  calc
    U + V + L + T = (U + L) + (T + V) := by abel
    _ = 0 := by rw [hl, hr, add_zero]
/-- 実混合候補の微分を、同じ候補の左右補正の合成と比較差で表す。 -/
lemma dgCommaAugmentationPrismMixedHom_differential_corrections
    (s : Simplex R (DGFunctorCommaObject R C E F) n)
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    let base := compose R
      (x := (s.obj a).replacement) (y := (s.obj b).replacement)
      (z := F.obj (s.obj b).source) (dgCommaAugmentationComponent R C E F (s.obj b)).val
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) (add_zero k)
    (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1)
      (dgCommaAugmentationPrismMixedHom R C E F s.toSimplexData β I a b k hI ha hb hk) =
    (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1) base +
    (∑ j ∈ Index.interior I a b, Index.sign I j •
      dgCommaAugmentationPrismCorrection R C E F s.toSimplexData β (I.erase j) a b (k + 1)) -
    (∑ l ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I l •
      dgCommaAugmentationImageCorrection R C E F s.toSimplexData β I a b k l) -
    (∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
      dgCommaAugmentationSuffixCorrection R C E F s.toSimplexData β I a b k j) -
    (∑ l ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I l •
      dgCommaAugmentationCutComparisonBoundary R C E F s.toSimplexData I a b k l) := by
  dsimp only
  have hc :
      (∑ j ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I j •
        dgCommaAugmentationCutQuadraticBoundary R C E F s.toSimplexData I a b k j) =
      -((∑ l ∈ dgCommaAugmentationCutPoints β I a b, Index.sign I l •
        dgCommaAugmentationImageCorrection R C E F s.toSimplexData β I a b k l) +
        (∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
          dgCommaAugmentationSuffixCorrection R C E F s.toSimplexData β I a b k j)) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_assoc] using
      dgCommaAugmentationCutQuadraticBoundary_corrections_cancel R C E F s.toSimplexData
        β I a b k hk
  rw [dgCommaAugmentationPrismMixedHom_differential_reduction R C E F s β I a b k
    hI ha hb hk, hc]
  abel
end SerrePositivity.InfinityCategories

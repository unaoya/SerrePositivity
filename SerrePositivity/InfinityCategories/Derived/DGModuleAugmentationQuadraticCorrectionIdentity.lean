module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationSuffixCorrection
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
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  {n : ℕ} (s : SimplexData R (DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ全実二次切断和は、候補の左右補正の同じ合成和と相殺する。 -/
lemma dgModuleAugmentationCutQuadraticBoundary_corrections_cancel
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I j •
      dgModuleAugmentationCutQuadraticBoundary R C E F s I a b k j) +
    (∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
      dgModuleAugmentationImageCorrection R C E F s β I a b k l) +
    (∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
      dgModuleAugmentationSuffixCorrection R C E F s β I a b k j) = 0 := by
  let U := ∑ j ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I j •
    ∑ l ∈ (Index.interior I a b).filter (j < ·), Index.sign (I.filter (j ≤ ·)) l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        dgModuleAugmentationNestedImageRight R C E F s I a b k j l)
  let V := ∑ l ∈ Index.interior I a b, Index.sign I l •
    ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
    ∑ j ∈ (Index.interior I a b).filter (· < l), Index.sign (I.filter (· ≤ l)) j •
      (if β l = 1 ∧ ¬ β j = 1 then
        dgModuleAugmentationNestedHomotopyLeft R C E F s I a b k j l else 0))
  let L := ∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
    dgModuleAugmentationImageCorrection R C E F s β I a b k l
  let T := ∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
    dgModuleAugmentationSuffixCorrection R C E F s β I a b k j
  have hq :
      (∑ j ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I j •
        dgModuleAugmentationCutQuadraticBoundary R C E F s I a b k j) = U + V :=
    dgModuleAugmentationCutQuadraticBoundary_sum_reduction R C E F s β I a b k hk
  have hl : U + L = 0 := dgModuleAugmentationImageCorrection_sum_cancel R C E F s β I a b k hk
  have hr : T + V = 0 := dgModuleAugmentationSuffixCorrection_sum_cancel R C E F s β I a b k hk
  change _ + L + T = 0
  rw [hq]
  calc
    U + V + L + T = (U + L) + (T + V) := by abel
    _ = 0 := by rw [hl, hr, add_zero]
/-- 実混合候補の微分を、同じ候補の左右補正の合成と比較差で表す。 -/
lemma dgModuleAugmentationPrismMixedHom_differential_corrections
    (s : Simplex R (DGModuleFunctorResolutionObject R C E F) n)
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    let base := compose R
      (x := (s.obj a).replacement.val) (y := (s.obj b).replacement.val)
      (z := F.obj (s.obj b).source) (dgModuleAugmentationComponent R C E F (s.obj b)).val
      (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj b)).f k
        (s.hom I a b k hI ha hb hk)) (add_zero k)
    (moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
      (dgModuleAugmentationPrismMixedHom R C E F s.toSimplexData β I a b k hI ha hb hk) =
    (moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1) base +
    (∑ j ∈ Index.interior I a b, Index.sign I j •
      dgModuleAugmentationPrismCorrection R C E F s.toSimplexData β (I.erase j) a b (k + 1)) -
    (∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
      dgModuleAugmentationImageCorrection R C E F s.toSimplexData β I a b k l) -
    (∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
      dgModuleAugmentationSuffixCorrection R C E F s.toSimplexData β I a b k j) -
    (∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
      dgModuleAugmentationCutComparisonBoundary R C E F s.toSimplexData I a b k l) := by
  dsimp only
  have hc :
      (∑ j ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I j •
        dgModuleAugmentationCutQuadraticBoundary R C E F s.toSimplexData I a b k j) =
      -((∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
        dgModuleAugmentationImageCorrection R C E F s.toSimplexData β I a b k l) +
        (∑ j ∈ (Index.interior I a b).filter (β · ≠ 1), Index.sign I j •
          dgModuleAugmentationSuffixCorrection R C E F s.toSimplexData β I a b k j)) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_assoc] using
      dgModuleAugmentationCutQuadraticBoundary_corrections_cancel R C E F s.toSimplexData
        β I a b k hk
  rw [dgModuleAugmentationPrismMixedHom_differential_reduction R C E F s β I a b k
    hI ha hb hk, hc]
  abel
end SerrePositivity.InfinityCategories

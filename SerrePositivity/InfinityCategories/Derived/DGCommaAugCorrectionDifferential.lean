module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugCutDifferentialExpansion
/-!
概要：実候補補正の全微分から線形二重和を消し、候補の全削除補正へ置き換える。
方針：同じ内部切断微分の三分解を有限和へ移し、実削除和の相殺を適用する。
規約：残る二次切断和・比較差の同定は別工程。
使われ方：実 prism の全 HA 方程式を、同じ二次境界の等式へ還元する。
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
  {n : ℕ} (s : Simplex R (DGFunctorCommaObject R C E F) n)
/-- 同じ候補補正の微分は、全削除補正・二次切断和・比較差の三項へ分解する。 -/
lemma dgCommaAugmentationPrismCorrection_differential
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) :
    (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1)
      (dgCommaAugmentationPrismCorrection R C E F s.toSimplexData β I a b k) =
    (∑ j ∈ Index.interior I a b, Index.sign I j •
      dgCommaAugmentationPrismCorrection R C E F s.toSimplexData β (I.erase j) a b (k + 1)) +
    (∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
      dgCommaAugmentationCutQuadraticBoundary R C E F s.toSimplexData I a b k l) -
    (∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
      dgCommaAugmentationCutComparisonBoundary R C E F s.toSimplexData I a b k l) := by
  have hd :
      (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1)
        (dgCommaAugmentationPrismCorrection R C E F s.toSimplexData β I a b k) =
      ∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
        (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1)
          (dgCommaAugmentationHomotopyCut R C E F s.toSimplexData I a b k l) := by
    simp only [dgCommaAugmentationPrismCorrection, Units.smul_def, map_sum, map_zsmul]
  have he :
      (∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
        (homObject R E (s.obj a).replacement (F.obj (s.obj b).source)).d k (k + 1)
          (dgCommaAugmentationHomotopyCut R C E F s.toSimplexData I a b k l)) =
      ∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
        (-dgCommaAugmentationCutLinearBoundary R C E F s.toSimplexData I a b k l +
          dgCommaAugmentationCutQuadraticBoundary R C E F s.toSimplexData I a b k l -
          dgCommaAugmentationCutComparisonBoundary R C E F s.toSimplexData I a b k l) := by
    apply Finset.sum_congr rfl
    intro l hl
    have hl' := Finset.mem_filter.mp hl
    rw [dgCommaAugmentationHomotopyCut_differential_expansion R C E F s I a b k
      hI ha hb hk l hl'.1 hl'.2.1 hl'.2.2.1]
  rw [hd, he]
  simp only [smul_sub, smul_add, smul_neg, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hl := dgCommaAugmentationPrismCorrection_linear_cancel R C E F s.toSimplexData
    β I a b k hk
  rw [← eq_neg_of_add_eq_zero_left hl]
/-- 実混合候補の微分から削除二重和を消し、同じ二次切断和と比較差だけを残す。 -/
lemma dgCommaAugmentationPrismMixedHom_differential_reduction
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
      dgCommaAugmentationPrismCorrection R C E F s.toSimplexData β (I.erase j) a b (k + 1)) +
    (∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
      dgCommaAugmentationCutQuadraticBoundary R C E F s.toSimplexData I a b k l) -
    (∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
      dgCommaAugmentationCutComparisonBoundary R C E F s.toSimplexData I a b k l) := by
  dsimp only
  rw [dgCommaAugmentationPrismMixedHom_eq_base_add_correction, map_add,
    dgCommaAugmentationPrismCorrection_differential R C E F s β I a b k hI ha hb hk]
  abel
end SerrePositivity.InfinityCategories

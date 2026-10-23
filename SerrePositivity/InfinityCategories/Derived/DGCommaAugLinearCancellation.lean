module
public import SerrePositivity.InfinityCategories.DGNerve.AugmentationCombinatorics
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugCutErasure
/-!
概要：同じ混合候補の全削除補正と、実切断の左右線形境界の符号和を相殺する。
方針：実削除係数の同定と、相一の切断点で支持を制限した混合符号相殺を使う。
規約：候補全体の HA 方程式や単体作用は別工程。
使われ方：実 prism 微分式の線形部分を候補の削除境界へ一致させる。
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
/-- 同じ実切断の左右線形境界の和。次数不一致の場合は零へ全域化する。 -/
def dgCommaAugmentationCutLinearBoundary
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (l : Fin (n + 1)) :
    GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k then
    compose R (x := (s.obj a).replacement) (y := (s.obj l).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgCommaAugmentationHomotopyAt R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1)
        (2 - ((I.filter (l ≤ ·)).card : ℤ)) (by omega)
        (s.linearBoundary (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.homOrZero (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega) +
    (2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
    compose R (x := (s.obj a).replacement) (y := (s.obj l).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgCommaAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ))
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.linearBoundary (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega)
  else 0
/-- 同じ左右線形境界は、一点削除後の同じ実切断の左右二和。 -/
lemma dgCommaAugmentationCutLinearBoundary_eq_erasedCuts
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (l : Fin (n + 1)) (hl : l ∈ I) (hal : a < l) (hlb : l < b) :
    dgCommaAugmentationCutLinearBoundary R C E F s I a b k l =
      (∑ j ∈ (Index.interior I a b).filter (l < ·), Index.sign (I.filter (l ≤ ·)) j •
        dgCommaAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        ∑ j ∈ (Index.interior I a b).filter (· < l), Index.sign (I.filter (· ≤ l)) j •
          dgCommaAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l := by
  have hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k := by
    have := Index.split_card hl
    omega
  rw [dgCommaAugmentationCutLinearBoundary, dite_eq_left hsum,
    dgCommaAugmentationHomotopyCut_linear_right R C E F s I a b k l hal hsum,
    dgCommaAugmentationHomotopyCut_linear_left R C E F s I a b k l hlb hsum]
/-- 全候補の削除補正は、同じ実切断の左右線形境界の符号和と相殺する。 -/
lemma dgCommaAugmentationPrismCorrection_linear_cancel
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ Index.interior I a b, Index.sign I j •
      dgCommaAugmentationPrismCorrection R C E F s β (I.erase j) a b (k + 1)) +
    (∑ l ∈ dgModuleAugmentationCutPoints β I a b, Index.sign I l •
      dgCommaAugmentationCutLinearBoundary R C E F s I a b k l) = 0 := by
  let K := Index.interior I a b
  have hcut :
      (∑ l ∈ K.filter (β · = 1), Index.sign I l •
        dgCommaAugmentationCutLinearBoundary R C E F s I a b k l) =
      (∑ l ∈ K.filter (β · = 1), Index.sign I l •
        ∑ j ∈ K.filter (l < ·), Index.sign (I.filter (l ≤ ·)) j •
          dgCommaAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l) +
      (∑ l ∈ K.filter (β · = 1), Index.sign I l •
        ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        ∑ j ∈ K.filter (· < l), Index.sign (I.filter (· ≤ l)) j •
          dgCommaAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    have hl' := Finset.mem_filter.mp (Finset.mem_filter.mp hl).1
    rw [dgCommaAugmentationCutLinearBoundary_eq_erasedCuts R C E F s I a b k hk
      l hl'.1 hl'.2.1 hl'.2.2, smul_add]
  rw [dgModuleAugmentationCutPoints_eq_filter_interior]
  change (∑ j ∈ K, Index.sign I j •
    dgCommaAugmentationPrismCorrection R C E F s β (I.erase j) a b (k + 1)) + _ = 0
  rw [hcut]
  simp only [dgCommaAugmentationPrismCorrection,
    dgModuleAugmentationCutPoints_eq_filter_interior, Index.interior_erase]
  have hh := dgModuleAugmentation_sum_mixed_cancel_filter I K (Finset.filter_subset _ _)
    (fun l ↦ β l = 1)
    (fun j l ↦ dgCommaAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l)
  simpa only [add_assoc] using hh
end SerrePositivity.InfinityCategories

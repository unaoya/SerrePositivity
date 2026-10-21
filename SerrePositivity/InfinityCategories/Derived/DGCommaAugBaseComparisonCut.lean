module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugQuadraticCorrectionIdentity
/-!
概要：実基底の切断合成と同じ比較差を、右入力像と左基底係数の合成へ移す。
方針：元の全 Hom chain map の成分、実比較差、通常順結合律を使う。
規約：切断係数を選び直さない。使われ方：候補の実二次境界における二相の照合。
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
/-- 同じ左基底係数に元の右入力像を後合成する全域切断係数。 -/
def dgCommaAugmentationImageBaseCut
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1)) :
    GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 then
    compose R (x := (s.obj a).replacement) (y := F.obj (s.obj j).source)
      (z := F.obj (s.obj b).source) (n := k + 1)
      ((dgFunctorCommaImageHomMap R C E F (s.obj j) (s.obj b)).f _
        (s.homOrZero (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ))))
      ((dgCommaAugmentationBaseHomMap R C E F (s.obj a) (s.obj j)).f _
        (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)))) h
  else 0
/-- 基底の実切断合成と同じ比較差の和は、右入力像と左基底の合成。 -/
lemma dgCommaAugmentationBaseCut_comparison
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ I) :
    (dgCommaAugmentationBaseHomMap R C E F (s.obj a) (s.obj b)).f (k + 1)
        (s.cutCompose I a b k j) +
      dgCommaAugmentationCutComparisonBoundary R C E F s I a b k j =
      dgCommaAugmentationImageBaseCut R C E F s I a b k j := by
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := Index.split_card hj
    omega
  have hsum' : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k := by omega
  rw [SimplexData.cutCompose, dite_eq_left hsum,
    dgCommaAugmentationCutComparisonBoundary, dite_eq_left hsum',
    dgCommaAugmentationImageBaseCut, dite_eq_left hsum,
    dgCommaAugmentationBaseHomMap_apply, dgCommaAugmentationBaseHomMap_apply,
    map_compose, dgCommaAugmentationBoundary_apply]
  let fl := s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ))
  let fr := s.homOrZero (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ))
  let bl := ((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _ fl
  let br := ((dgCommaAugmentationSource R C E F).map (s.obj j) (s.obj b)).f _ fr
  let gr := (dgFunctorCommaImageHomMap R C E F (s.obj j) (s.obj b)).f _ fr
  have hb := compose_assoc_of_sum (A := R) (D := E)
    (w := (s.obj a).replacement) (x := (s.obj j).replacement)
    (y := (s.obj b).replacement) (z := F.obj (s.obj b).source) bl br
    (dgCommaAugmentationComponent R C E F (s.obj b)).val
    hsum (add_zero _) (add_zero _)
  have hi := compose_assoc_of_sum (A := R) (D := E)
    (w := (s.obj a).replacement) (x := (s.obj j).replacement)
    (y := F.obj (s.obj j).source) (z := F.obj (s.obj b).source) bl
    (dgCommaAugmentationComponent R C E F (s.obj j)).val gr
    (add_zero _) (zero_add _) hsum
  change compose R (x := (s.obj a).replacement) (y := (s.obj b).replacement)
      (z := F.obj (s.obj b).source) (dgCommaAugmentationComponent R C E F (s.obj b)).val
      (compose R (x := (s.obj a).replacement) (y := (s.obj j).replacement)
        (z := (s.obj b).replacement) br bl hsum) (add_zero _) +
    compose R (x := (s.obj a).replacement) (y := (s.obj j).replacement)
      (z := F.obj (s.obj b).source)
      (compose R (x := (s.obj j).replacement) (y := F.obj (s.obj j).source)
          (z := F.obj (s.obj b).source) gr
          (dgCommaAugmentationComponent R C E F (s.obj j)).val (zero_add _) -
        compose R (x := (s.obj j).replacement) (y := (s.obj b).replacement)
          (z := F.obj (s.obj b).source)
          (dgCommaAugmentationComponent R C E F (s.obj b)).val br (add_zero _)) bl hsum =
    compose R (x := (s.obj a).replacement) (y := F.obj (s.obj j).source)
      (z := F.obj (s.obj b).source) gr
      (compose R (x := (s.obj a).replacement) (y := (s.obj j).replacement)
        (z := F.obj (s.obj j).source)
        (dgCommaAugmentationComponent R C E F (s.obj j)).val bl (add_zero _)) hsum
  rw [hb, hi, compose_sub_left]
  abel
end SerrePositivity.InfinityCategories

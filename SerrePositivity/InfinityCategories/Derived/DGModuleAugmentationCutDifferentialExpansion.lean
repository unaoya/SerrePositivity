module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationLinearCancellation
/-!
概要：元の同じ実単体の HA を代入した切断微分を、線形・二次・比較差に分解する。
方針：左右の線形性と同じ次数符号を整理し、前工程の実切断微分式を使う。
規約：実係数の微分を計算する。使われ方：候補全体の HA の二次部分への還元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
private lemma augmentation_compose_neg_left (R : Type u) [CommRing R]
    {D : Type v} [DGCategory R D] {x y z : D} {p q k : ℤ}
    (g : GradedHom R y z q) (f : GradedHom R x y p) (h : p + q = k) :
    compose R (-g) f h = -(compose R g f h) := by
  simpa [Units.smul_def] using compose_units_smul_left (-1) g f h
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  {n : ℕ} (s : SimplexData R (DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ実切断の左右二次境界の和。 -/
def dgModuleAugmentationCutQuadraticBoundary
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (l : Fin (n + 1)) :
    GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k then
    compose R (x := (s.obj a).replacement.val) (y := (s.obj l).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgModuleAugmentationHomotopyAt R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1)
        (2 - ((I.filter (l ≤ ·)).card : ℤ)) (by omega)
        (s.quadraticBoundary (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.homOrZero (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega) +
    (2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
    compose R (x := (s.obj a).replacement.val) (y := (s.obj l).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgModuleAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ))
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.quadraticBoundary (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega)
  else 0
/-- 同じ実切断の比較差と左入力像の合成。 -/
def dgModuleAugmentationCutComparisonBoundary
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (l : Fin (n + 1)) :
    GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k then
    compose R (x := (s.obj a).replacement.val) (y := (s.obj l).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      ((dgModuleFunctorResolutionBoundary R C E F (s.obj l) (s.obj b)).f
        (2 - ((I.filter (l ≤ ·)).card : ℤ))
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.homOrZero (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega)
  else 0
/-- 元の実単体の同じ切断微分は、負の左右線形境界・左右二次境界・負の比較差。 -/
lemma dgModuleAugmentationHomotopyCut_differential_expansion
    (s : Simplex R (DGModuleFunctorResolutionObject R C E F) n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (Index.nonempty hI)) (hb : b = I.max' (Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (l : Fin (n + 1))
    (hl : l ∈ I) (hal : a < l) (hlb : l < b) :
    (moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
        (dgModuleAugmentationHomotopyCut R C E F s.toSimplexData I a b k l) =
      -dgModuleAugmentationCutLinearBoundary R C E F s.toSimplexData I a b k l +
        dgModuleAugmentationCutQuadraticBoundary R C E F s.toSimplexData I a b k l -
        dgModuleAugmentationCutComparisonBoundary R C E F s.toSimplexData I a b k l := by
  have hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k := by
    have := Index.split_card hl
    omega
  rw [dgModuleAugmentationHomotopyCut_simplex_boundary R C E F s I a b k l
    hI ha hb hk hl hal hlb]
  dsimp only
  simp only [dgModuleAugmentationCutLinearBoundary, dgModuleAugmentationCutQuadraticBoundary,
    dgModuleAugmentationCutComparisonBoundary, dite_eq_left hsum]
  simp only [dgModuleAugmentationHomotopyAt, map_sub, augmentation_compose_neg_left,
    compose_sub_right,
    Int.negOnePow_sub, Int.negOnePow_one, mul_neg_one, Units.neg_smul, smul_sub]
  simp only [compose, forward, TensorProduct.tmul_add, TensorProduct.tmul_sub,
    map_add, map_sub, smul_add, smul_sub]
  abel
end SerrePositivity.InfinityCategories

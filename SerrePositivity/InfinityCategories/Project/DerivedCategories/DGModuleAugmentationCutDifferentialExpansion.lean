module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationLinearCancellation
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
private lemma augmentation_compose_neg_left (R : Type u) [CommRing R]
    {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y z : D} {p q k : ℤ}
    (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R y z q) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x y p) (h : p + q = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R (-g) f h = -(_root_.SerrePositivity.DifferentialGraded.compose R g f h) := by
  simpa [Units.smul_def] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left (-1) g f h
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ実切断の左右二次境界の和。 -/
def dgModuleAugmentationCutQuadraticBoundary
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (l : Fin (n + 1)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k then
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := (s.obj l).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1)
        (2 - ((I.filter (l ≤ ·)).card : ℤ)) (by omega)
        (s.quadraticBoundary (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.homOrZero (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega) +
    (2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := (s.obj l).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ))
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.quadraticBoundary (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega)
  else 0
/-- 同じ実切断の比較差と左入力像の合成。 -/
def dgModuleAugmentationCutComparisonBoundary
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (l : Fin (n + 1)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k then
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := (s.obj l).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionBoundary R C E F (s.obj l) (s.obj b)).f
        (2 - ((I.filter (l ≤ ·)).card : ℤ))
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.homOrZero (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega)
  else 0
/-- 元の実単体の同じ切断微分は、負の左右線形境界・左右二次境界・負の比較差。 -/
lemma dgModuleAugmentationHomotopyCut_differential_expansion
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ)) (l : Fin (n + 1))
    (hl : l ∈ I) (hal : a < l) (hlb : l < b) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R E (s.obj a).replacement.val (F.obj (s.obj b).source)).d k (k + 1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s.toSimplexData I a b k l) =
      -_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutLinearBoundary R C E F s.toSimplexData I a b k l +
        dgModuleAugmentationCutQuadraticBoundary R C E F s.toSimplexData I a b k l -
        dgModuleAugmentationCutComparisonBoundary R C E F s.toSimplexData I a b k l := by
  have hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hl
    omega
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut_simplex_boundary R C E F s I a b k l
    hI ha hb hk hl hal hlb]
  dsimp only
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationCutLinearBoundary, dgModuleAugmentationCutQuadraticBoundary,
    dgModuleAugmentationCutComparisonBoundary, dite_eq_left hsum]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt, map_sub, augmentation_compose_neg_left,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right,
    Int.negOnePow_sub, Int.negOnePow_one, mul_neg_one, Units.neg_smul, smul_sub]
  simp only [_root_.SerrePositivity.DifferentialGraded.compose, _root_.SerrePositivity.DifferentialGraded.forward, TensorProduct.tmul_add, TensorProduct.tmul_sub,
    map_add, map_sub, smul_add, smul_sub]
  abel
end SerrePositivity.InfinityCategories.Project.DerivedCategories

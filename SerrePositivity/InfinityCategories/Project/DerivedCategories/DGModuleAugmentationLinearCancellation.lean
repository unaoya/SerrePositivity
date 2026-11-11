module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AugmentationCombinatorics
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationCutErasure
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) n)
/-- 同じ実切断の左右線形境界の和。次数不一致の場合は零へ全域化する。 -/
def dgModuleAugmentationCutLinearBoundary
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (l : Fin (n + 1)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k then
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := (s.obj l).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyAt R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1)
        (2 - ((I.filter (l ≤ ·)).card : ℤ)) (by omega)
        (s.linearBoundary (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
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
        (s.linearBoundary (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega)
  else 0
/-- 同じ左右線形境界は、一点削除後の同じ実切断の左右二和。 -/
lemma dgModuleAugmentationCutLinearBoundary_eq_erasedCuts
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (l : Fin (n + 1)) (hl : l ∈ I) (hal : a < l) (hlb : l < b) :
    dgModuleAugmentationCutLinearBoundary R C E F s I a b k l =
      (∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (l < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (l ≤ ·)) j •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l := by
  have hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hl
    omega
  rw [dgModuleAugmentationCutLinearBoundary, dite_eq_left hsum,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut_linear_right R C E F s I a b k l hal hsum,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut_linear_left R C E F s I a b k l hlb hsum]
/-- 全候補の削除補正は、同じ実切断の左右線形境界の符号和と相殺する。 -/
lemma dgModuleAugmentationPrismCorrection_linear_cancel
    (β : Fin (n + 1) →o Fin 2) (I : Finset (Fin (n + 1)))
    (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ)) :
    (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCorrection R C E F s β (I.erase j) a b (k + 1)) +
    (∑ l ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints β I a b, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
      dgModuleAugmentationCutLinearBoundary R C E F s I a b k l) = 0 := by
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b
  have hcut :
      (∑ l ∈ K.filter (β · = 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
        dgModuleAugmentationCutLinearBoundary R C E F s I a b k l) =
      (∑ l ∈ K.filter (β · = 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
        ∑ j ∈ K.filter (l < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (l ≤ ·)) j •
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l) +
      (∑ l ∈ K.filter (β · = 1), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I l •
        ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        ∑ j ∈ K.filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    have hl' := Finset.mem_filter.mp (Finset.mem_filter.mp hl).1
    rw [dgModuleAugmentationCutLinearBoundary_eq_erasedCuts R C E F s I a b k hk
      l hl'.1 hl'.2.1 hl'.2.2, smul_add]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints_eq_filter_interior]
  change (∑ j ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j •
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCorrection R C E F s β (I.erase j) a b (k + 1)) + _ = 0
  rw [hcut]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationPrismCorrection,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentationCutPoints_eq_filter_interior, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior_erase]
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgModuleAugmentation_sum_mixed_cancel_filter I K (Finset.filter_subset _ _)
    (fun l ↦ β l = 1)
    (fun j l ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l)
  simpa only [add_assoc] using hh
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AugmentationCombinatorics
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCommaAugCutBoundary
/-!
概要：実切断の左右の削除を同じ合成へ同定し、線形境界を削除和へ移す。
方針：片側の切断集合の不変性と濃度の変化、同じ比較成分の次数輸送を使う。
規約：元の実係数を保持する。使われ方：augmentation 補正の全削除和の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E)
  {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) n)
/-- 右側の一点削除後の実切断は、同じ右削除係数と左像の合成。 -/
lemma dgCommaAugmentationHomotopyCut_erase_right
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (j l : Fin (n + 1)) (hj : j ∈ I) (hlj : l < j)
    (hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l =
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement) (y := (s.obj l).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyAt R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1)
        (2 - ((I.filter (l ≤ ·)).card : ℤ)) (by omega)
        (s.homOrZero ((I.filter (l ≤ ·)).erase j) l b
          (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1)))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.homOrZero (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega) := by
  have hL : (I.erase j).filter (· ≤ l) = I.filter (· ≤ l) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_le_of_gt hlj
  have hjR : j ∈ I.filter (l ≤ ·) := Finset.mem_filter.mpr ⟨hj, hlj.le⟩
  have hdeg : 2 - (((I.filter (l ≤ ·)).erase j).card : ℤ) =
      2 - ((I.filter (l ≤ ·)).card : ℤ) + 1 := by
    have := Finset.card_erase_add_one hjR
    omega
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyCut
  rw [hL, Finset.filter_erase, hdeg, dite_eq_left (by omega)]
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq rfl rfl rfl rfl (by omega) rfl _ _ _ _ ?_ (HEq.rfl) _ _
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyAt_heq R C E F (s.obj l) (s.obj b)
    (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1) (2 - ((I.filter (l ≤ ·)).card : ℤ))
    (by omega) (s.homOrZero ((I.filter (l ≤ ·)).erase j) l b _)).symm
/-- 左側の一点削除後の実切断は、同じ右比較成分と左削除像の合成。 -/
lemma dgCommaAugmentationHomotopyCut_erase_left
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (j l : Fin (n + 1)) (hj : j ∈ I) (hjl : j < l)
    (hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l =
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement) (y := (s.obj l).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ))
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.homOrZero ((I.filter (· ≤ l)).erase j) a l
          (2 - ((I.filter (· ≤ l)).card : ℤ) + 1))) (by omega) := by
  have hR : (I.erase j).filter (l ≤ ·) = I.filter (l ≤ ·) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and]
    intro _
    exact not_le_of_gt hjl
  have hjL : j ∈ I.filter (· ≤ l) := Finset.mem_filter.mpr ⟨hj, hjl.le⟩
  have hdeg : 2 - (((I.filter (· ≤ l)).erase j).card : ℤ) =
      2 - ((I.filter (· ≤ l)).card : ℤ) + 1 := by
    have := Finset.card_erase_add_one hjL
    omega
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyCut
  rw [hR, Finset.filter_erase, hdeg, dite_eq_left (by omega)]
/-- 右線形境界の同じ比較成分との合成は、右側の削除後の実切断和。 -/
lemma dgCommaAugmentationHomotopyCut_linear_right
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (l : Fin (n + 1)) (hal : a < l)
    (hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement) (y := (s.obj l).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyAt R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ) + 1)
        (2 - ((I.filter (l ≤ ·)).card : ℤ)) (by omega)
        (s.linearBoundary (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.homOrZero (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega) =
    ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (l < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (l ≤ ·)) j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyAt_linearBoundary]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior_right_cut I a b l hal]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := Finset.mem_filter.mp hj
  have hjI := (Finset.mem_filter.mp hm.1).1
  rw [dgCommaAugmentationHomotopyCut_erase_right R C E F s I a b k j l hjI hm.2 hsum]
/-- 左線形境界の同じ入力像との合成は、左側の削除後の実切断和。 -/
lemma dgCommaAugmentationHomotopyCut_linear_left
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (l : Fin (n + 1)) (hlb : l < b)
    (hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) = k) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement) (y := (s.obj l).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ))
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.linearBoundary (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega) =
    ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyCut R C E F s (I.erase j) a b (k + 1) l := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.linearBoundary, Units.smul_def, map_sum, map_zsmul,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior_left_cut I a b l hlb]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := Finset.mem_filter.mp hj
  have hjI := (Finset.mem_filter.mp hm.1).1
  rw [dgCommaAugmentationHomotopyCut_erase_left R C E F s I a b k j l hjI hm.2 hsum]
  simpa only [Units.smul_def] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b) _
      (s.homOrZero (I.filter (l ≤ ·)) l b _))
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
      (s.homOrZero ((I.filter (· ≤ l)).erase j) a l _)) (by omega)
end SerrePositivity.InfinityCategories.Project.DerivedCategories

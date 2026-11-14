module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugCorrectionDifferential
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugNestedImageCut
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AugmentationCombinatorics
/-!
概要：実二次切断境界を、中央比較補正と右比較補正を持つ同じ三重合成へ展開する。
方針：元の実二次境界の全有限和へ斉次合成則を適用し、内部点集合をそろえる。
規約：すべて同じ実係数を使う。使われ方：全候補 HA の二重切断和と相付き相殺の接続。
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
/-- 右二次境界との同じ比較合成は、中央比較・右比較の実三重合成の二和。 -/
lemma dgCommaAugmentationQuadraticCut_right
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1))
    (haj : a < j)
    (hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement) (y := (s.obj j).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyAt R C E F (s.obj j) (s.obj b)
        (2 - ((I.filter (j ≤ ·)).card : ℤ) + 1)
        (2 - ((I.filter (j ≤ ·)).card : ℤ)) (by omega)
        (s.quadraticBoundary (I.filter (j ≤ ·)) j b (2 - ((I.filter (j ≤ ·)).card : ℤ))))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
        (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)))) hsum =
    ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedImageRight R C E F s I a b k j l +
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyRight R C E F s I a b k j l) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyAt_quadraticBoundary R C E F s
    (I.filter (j ≤ ·)) j b _ rfl]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior_right_cut I a b j haj]
  apply Finset.sum_congr rfl
  intro l hl
  have hjl := (Finset.mem_filter.mp hl).2
  have hRR : (I.filter (j ≤ ·)).filter (l ≤ ·) = I.filter (l ≤ ·) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hjl.le.trans h.2⟩, h.2⟩⟩
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedImageRight, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyRight,
    dite_eq_left hsum, hRR]
/-- 左二次境界の同じ入力像との比較合成は、左からの同じ実二重切断和。 -/
lemma dgCommaAugmentationQuadraticCut_left
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (l : Fin (n + 1))
    (hlb : l < b)
    (hsum : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1) :
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement) (y := (s.obj l).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b)
        (2 - ((I.filter (l ≤ ·)).card : ℤ))
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
        (s.quadraticBoundary (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ))))
      (by omega) =
    ∑ j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < l), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j •
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.quadraticBoundary, Units.smul_def, map_sum, map_zsmul,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior_left_cut I a b l hlb]
  apply Finset.sum_congr rfl
  intro j _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyLeft, dite_eq_left hsum]
  simpa only [Units.smul_def] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ l)) j)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b) _
      (s.homOrZero (I.filter (l ≤ ·)) l b _))
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj l)).f _
      (s.cutCompose (I.filter (· ≤ l)) a l _ j)) (by omega)
/-- 同じ実二次切断境界は、左右の全三重合成へ展開される。 -/
lemma dgCommaAugmentationCutQuadraticBoundary_expansion
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ I) (haj : a < j) (hjb : j < b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationCutQuadraticBoundary R C E F s I a b k j =
    (∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (j < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) l •
      ((2 - ((I.filter (l ≤ ·)).card : ℤ)).negOnePow •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedImageRight R C E F s I a b k j l +
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyRight R C E F s I a b k j l)) +
    (2 - ((I.filter (j ≤ ·)).card : ℤ)).negOnePow •
      ∑ l ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I a b).filter (· < j), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ j)) l •
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k l j := by
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  have hsum' : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k := by omega
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationCutQuadraticBoundary, dite_eq_left hsum',
    dgCommaAugmentationQuadraticCut_right R C E F s I a b k j haj hsum,
    dgCommaAugmentationQuadraticCut_left R C E F s I a b k j hjb hsum]
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CommaCategories.DGCommaAugNestedHomotopyCut
/-!
概要：中央比較成分と左右の実入力像を持つ二重切断を、二つの切断順で同定する。
方針：同じ三つの区間と次数へそろえ、通常順三重合成の結合律を使う。
規約：比較成分を選び直さない。使われ方：二次切断の像補正を候補の左補正へ移す。
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
/-- 右部分集合の中央比較補正と、元の左入力像を合成する二重切断。 -/
def dgCommaAugmentationNestedImageRight
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j l : Fin (n + 1)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 then
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement) (y := (s.obj j).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationImageCut R C E F s (I.filter (j ≤ ·)) j b
        (2 - ((I.filter (j ≤ ·)).card : ℤ)) l)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
        (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)))) h
  else 0
/-- 左部分集合の同じ切断補正に、元の右入力像を合成する二重切断。 -/
def dgCommaAugmentationNestedImageLeft
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j l : Fin (n + 1)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 then
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement) (y := F.obj (s.obj l).source)
      (z := F.obj (s.obj b).source) (n := k + 1)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaImageHomMap R C E F (s.obj l) (s.obj b)).f _
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyCut R C E F s (I.filter (· ≤ l)) a l
        (2 - ((I.filter (· ≤ l)).card : ℤ)) j) h
  else 0
/-- 二つの切断順は、同じ中央比較成分と同じ左右入力像の三重合成を与える。 -/
lemma dgCommaAugmentationNestedImageRight_eq_left
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (j l : Fin (n + 1)) (hj : j ∈ I) (hl : l ∈ I) (hjl : j < l) :
    dgCommaAugmentationNestedImageRight R C E F s I a b k j l =
      dgCommaAugmentationNestedImageLeft R C E F s I a b k j l := by
  have hsumj : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hj
    omega
  have hsuml : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 := by
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hl
    omega
  have hRR : (I.filter (j ≤ ·)).filter (l ≤ ·) = I.filter (l ≤ ·) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hjl.le.trans h.2⟩, h.2⟩⟩
  have hLL : (I.filter (· ≤ l)).filter (· ≤ j) = I.filter (· ≤ j) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.trans hjl.le⟩, h.2⟩⟩
  have hM : (I.filter (· ≤ l)).filter (j ≤ ·) = (I.filter (j ≤ ·)).filter (· ≤ l) := by
    ext x
    simp only [Finset.mem_filter]
    tauto
  have hjL : j ∈ I.filter (· ≤ l) := Finset.mem_filter.mpr ⟨hj, hjl.le⟩
  have hlR : l ∈ I.filter (j ≤ ·) := Finset.mem_filter.mpr ⟨hl, hjl.le⟩
  have hleft : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - (((I.filter (j ≤ ·)).filter (· ≤ l)).card : ℤ) - 1) =
      (2 - ((I.filter (· ≤ l)).card : ℤ)) := by
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hjL
    rw [hLL, hM] at hc
    omega
  have hright : (2 - (((I.filter (j ≤ ·)).filter (· ≤ l)).card : ℤ) - 1) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) =
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) := by
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hlR
    rw [hRR] at hc
    omega
  rw [dgCommaAugmentationNestedImageRight, dgCommaAugmentationNestedImageLeft,
    dite_eq_left hsumj, dite_eq_left hsuml]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationImageCut _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationHomotopyCut
  rw [hRR, hLL, hM, dite_eq_left hright, dite_eq_left hleft]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ hleft hright (by omega)).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories

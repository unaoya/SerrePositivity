module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationBaseBoundary
/-!
概要：同じ右比較成分を持つ二重切断を、二つの切断順で同定する。
方針：三つの実区間と中間次数をそろえ、実入力像の合成保存と通常順結合律を使う。
規約：全域係数の同じ値を保持する。使われ方：二次切断和の同相部分の相殺。
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
/-- 右部分集合の実切断補正と元の左入力像を合成する二重切断。 -/
def dgModuleAugmentationNestedHomotopyRight
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j l : Fin (n + 1)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 then
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut R C E F s (I.filter (j ≤ ·)) j b
        (2 - ((I.filter (j ≤ ·)).card : ℤ)) l)
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
        (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)))) h
  else 0
/-- 同じ右比較成分に、左部分集合の実切断合成の入力像を合成する二重切断。 -/
def dgModuleAugmentationNestedHomotopyLeft
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j l : Fin (n + 1)) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj a).replacement.val (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 then
    _root_.SerrePositivity.DifferentialGraded.compose R (x := (s.obj a).replacement.val) (y := (s.obj l).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b) _
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj l)).f
        (2 - ((I.filter (· ≤ l)).card : ℤ) + 1)
        (s.cutCompose (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ)) j))
      (by omega)
  else 0
/-- 二つの実切断順は、同じ右比較成分と同じ二入力像の三重合成を与える。 -/
lemma dgModuleAugmentationNestedHomotopyRight_eq_left
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (j l : Fin (n + 1)) (hj : j ∈ I) (hl : l ∈ I) (hjl : j < l) :
    dgModuleAugmentationNestedHomotopyRight R C E F s I a b k j l =
      dgModuleAugmentationNestedHomotopyLeft R C E F s I a b k j l := by
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
      (2 - (((I.filter (j ≤ ·)).filter (· ≤ l)).card : ℤ)) =
      (2 - ((I.filter (· ≤ l)).card : ℤ)) + 1 := by
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hjL
    rw [hLL, hM] at hc
    omega
  have hright : (2 - (((I.filter (j ≤ ·)).filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) =
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) := by
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.split_card hlR
    rw [hRR] at hc
    omega
  rw [dgModuleAugmentationNestedHomotopyRight, dgModuleAugmentationNestedHomotopyLeft,
    dite_eq_left hsumj, dite_eq_left hsuml]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationHomotopyCut _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cutCompose
  rw [hRR, hLL, hM, dite_eq_left hright, dite_eq_left hleft, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ hleft hright (by omega)).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories

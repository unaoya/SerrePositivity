module
public import SerrePositivity.InfinityCategories.Derived.DGCommaAugBaseBoundary
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  {n : ℕ} (s : SimplexData R (DGFunctorCommaObject R C E F) n)
/-- 右部分集合の実切断補正と元の左入力像を合成する二重切断。 -/
def dgCommaAugmentationNestedHomotopyRight
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j l : Fin (n + 1)) :
    GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 then
    compose R (x := (s.obj a).replacement) (y := (s.obj j).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgCommaAugmentationHomotopyCut R C E F s (I.filter (j ≤ ·)) j b
        (2 - ((I.filter (j ≤ ·)).card : ℤ)) l)
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj j)).f _
        (s.homOrZero (I.filter (· ≤ j)) a j (2 - ((I.filter (· ≤ j)).card : ℤ)))) h
  else 0
/-- 同じ右比較成分に、左部分集合の実切断合成の入力像を合成する二重切断。 -/
def dgCommaAugmentationNestedHomotopyLeft
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j l : Fin (n + 1)) :
    GradedHom R (s.obj a).replacement (F.obj (s.obj b).source) (k + 1) :=
  if h : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 then
    compose R (x := (s.obj a).replacement) (y := (s.obj l).replacement)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (dgCommaAugmentationHomotopyComponent R C E F (s.obj l) (s.obj b) _
        (s.homOrZero (I.filter (l ≤ ·)) l b (2 - ((I.filter (l ≤ ·)).card : ℤ))))
      (((dgCommaAugmentationSource R C E F).map (s.obj a) (s.obj l)).f
        (2 - ((I.filter (· ≤ l)).card : ℤ) + 1)
        (s.cutCompose (I.filter (· ≤ l)) a l (2 - ((I.filter (· ≤ l)).card : ℤ)) j))
      (by omega)
  else 0
/-- 二つの実切断順は、同じ右比較成分と同じ二入力像の三重合成を与える。 -/
lemma dgCommaAugmentationNestedHomotopyRight_eq_left
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hk : k = 2 - (I.card : ℤ))
    (j l : Fin (n + 1)) (hj : j ∈ I) (hl : l ∈ I) (hjl : j < l) :
    dgCommaAugmentationNestedHomotopyRight R C E F s I a b k j l =
      dgCommaAugmentationNestedHomotopyLeft R C E F s I a b k j l := by
  have hsumj : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := Index.split_card hj
    omega
  have hsuml : (2 - ((I.filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ)) = k + 1 := by
    have := Index.split_card hl
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
    have hc := Index.split_card hjL
    rw [hLL, hM] at hc
    omega
  have hright : (2 - (((I.filter (j ≤ ·)).filter (· ≤ l)).card : ℤ)) +
      (2 - ((I.filter (l ≤ ·)).card : ℤ) - 1) =
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) := by
    have hc := Index.split_card hlR
    rw [hRR] at hc
    omega
  rw [dgCommaAugmentationNestedHomotopyRight, dgCommaAugmentationNestedHomotopyLeft,
    dite_eq_left hsumj, dite_eq_left hsuml]
  unfold dgCommaAugmentationHomotopyCut SimplexData.cutCompose
  rw [hRR, hLL, hM, dite_eq_left hright, dite_eq_left hleft, map_compose]
  exact (compose_assoc_of_sum _ _ _ hleft hright (by omega)).symm
end SerrePositivity.InfinityCategories

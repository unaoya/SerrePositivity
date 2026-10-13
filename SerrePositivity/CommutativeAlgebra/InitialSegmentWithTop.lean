module

public import Mathlib.Order.WithBot
public import Mathlib.Order.Hom.Basic

/-! # 初期部分への終点追加

任意の線形順序で、開初期部分へ終点を加えた添字は閉初期部分と順序同型。
最小元の場合も開初期部分が空であるだけなので同じ同型を使う。
-/

@[expose] public section
namespace SerrePositivity
variable {ι : Type*} [LinearOrder ι]

/-- 開初期部分に終点を追加した添字を、閉初期部分へ送る。 -/
def initialSegmentWithTopMap (i : ι) : WithTop {j : ι // j < i} → {j : ι // j ≤ i} :=
  WithTop.recTopCoe ⟨i, le_rfl⟩ (fun j ↦ ⟨j.val, j.property.le⟩)

@[simp] theorem initialSegmentWithTopMap_top (i : ι) :
    initialSegmentWithTopMap i ⊤ = ⟨i, le_rfl⟩ := rfl

@[simp] theorem initialSegmentWithTopMap_coe (i : ι) (j : {j : ι // j < i}) :
    initialSegmentWithTopMap i (j : WithTop {j : ι // j < i}) = ⟨j.val, j.property.le⟩ := rfl

/-- 閉初期部分の終点をtopへ、それ以外を旧添字へ戻す。 -/
def initialSegmentWithTopInv (i : ι) (j : {j : ι // j ≤ i}) : WithTop {j : ι // j < i} :=
  if h : j.val = i then ⊤ else (⟨j.val, lt_of_le_of_ne j.property h⟩ : {j : ι // j < i})

/-- WithTop(Iio i)をIic iへ移す具体的な順序同型。 -/
def initialSegmentWithTopEquiv (i : ι) :
    WithTop ({j : ι // j < i}) ≃o {j : ι // j ≤ i} where
  toFun := initialSegmentWithTopMap i
  invFun := initialSegmentWithTopInv i
  left_inv x := by
    cases x with
    | top =>
      rw [initialSegmentWithTopMap_top]
      unfold initialSegmentWithTopInv
      rw [dite_eq_left rfl]
    | coe j =>
      rw [initialSegmentWithTopMap_coe]
      unfold initialSegmentWithTopInv
      rw [dite_eq_right j.property.ne]
  right_inv j := by
    unfold initialSegmentWithTopInv
    by_cases h : j.val = i
    · rw [dite_eq_left h, initialSegmentWithTopMap_top]
      exact Subtype.ext h.symm
    · rw [dite_eq_right h, initialSegmentWithTopMap_coe]
  map_rel_iff' := by
    intro x y
    cases x with
    | top =>
      cases y with
      | top => simp
      | coe j =>
        change i ≤ j.val ↔ (⊤ : WithTop ({j : ι // j < i})) ≤ ↑j
        simp only [WithTop.not_top_le_coe, iff_false]
        exact not_le_of_gt j.property
    | coe j =>
      cases y with
      | top =>
        change j.val ≤ i ↔ (j : WithTop ({j : ι // j < i})) ≤ ⊤
        exact iff_of_true j.property.le le_top
      | coe k =>
        change j ≤ k ↔ (j : WithTop ({j : ι // j < i})) ≤ k
        exact WithTop.coe_le_coe.symm

@[simp] theorem initialSegmentWithTopEquiv_top (i : ι) :
    initialSegmentWithTopEquiv i ⊤ = ⟨i, le_rfl⟩ := rfl

@[simp] theorem initialSegmentWithTopEquiv_coe (i : ι) (j : {j : ι // j < i}) :
    initialSegmentWithTopEquiv i (j : WithTop ({j : ι // j < i})) = ⟨j.val, j.property.le⟩ := rfl

@[simp] theorem initialSegmentWithTopEquiv_symm_top (i : ι) :
    (initialSegmentWithTopEquiv i).symm ⟨i, le_rfl⟩ = ⊤ := by
  exact (initialSegmentWithTopEquiv i).symm_apply_apply ⊤

@[simp] theorem initialSegmentWithTopEquiv_symm_coe (i : ι) (j : {j : ι // j < i}) :
    (initialSegmentWithTopEquiv i).symm ⟨j.val, j.property.le⟩ =
      (j : WithTop ({j : ι // j < i})) := by
  exact (initialSegmentWithTopEquiv i).symm_apply_apply j

end SerrePositivity

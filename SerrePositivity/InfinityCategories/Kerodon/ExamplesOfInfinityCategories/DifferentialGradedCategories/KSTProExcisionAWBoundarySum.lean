module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWBoundaryCoordinates

/-!
# AW の実境界和の非対角項の並べ替え

概要：入れ子の水平・垂直境界和を、削除点と削除後の切断点の二重和へ移す。
方針：各境界の座標の同値と、左右の非対角境界の添字の同値を合成する。
規約：KST Construction A.5 の標準 AW、符号を含む任意の加法的な項に使える。
使われ方：全切断点での鎖写像性の有限和の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：左右の入れ子の非対角境界和は削除後の切断の二重和に一致。
方針：水平・垂直の座標の同値から境界添字の同値へ有限和を移す。
規約：KST A.5、任意の可換加法モノイドに成立。
使われ方：実 AW の境界和の最後の並べ替え。 -/
lemma awBoundaryCoordinates_sum {A : Type*} [AddCommMonoid A] (n : ℕ)
    (F : Fin (n + 2) × Fin (n + 1) → A) :
    (∑ i : Fin (n + 1), ∑ k : Fin ((i : ℕ) + 1),
      F (⟨k, by have := k.isLt; have := i.isLt; omega⟩, i)) +
    (∑ i : Fin (n + 1), ∑ k : Fin (n - (i : ℕ) + 1),
      F (⟨(i : ℕ) + ((k : ℕ) + 1), by have := k.isLt; have := i.isLt; omega⟩, i)) =
    ∑ k : Fin (n + 2), ∑ i : Fin (n + 1), F (k, i) := by
  have hL := Fintype.sum_equiv (awLeftBoundaryCoordinates n)
    (fun x ↦ F (awBoundaryIndexForward n (.inl (awLeftBoundaryCoordinates n x))))
    (fun x ↦ F (awBoundaryIndexForward n (.inl x))) (fun _ ↦ rfl)
  have hR := Fintype.sum_equiv (awRightBoundaryCoordinates n)
    (fun x ↦ F (awBoundaryIndexForward n (.inr (awRightBoundaryCoordinates n x))))
    (fun x ↦ F (awBoundaryIndexForward n (.inr x))) (fun _ ↦ rfl)
  have h := awBoundaryIndex_sum n F
  rw [← hL, ← hR] at h
  simpa [Fintype.sum_sigma, awLeftBoundaryCoordinates, awRightBoundaryCoordinates,
    awBoundaryIndexForward] using h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

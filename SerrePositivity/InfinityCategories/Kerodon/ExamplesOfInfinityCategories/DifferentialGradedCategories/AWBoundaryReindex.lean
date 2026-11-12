module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWBoundaryMatch

/-!
# AW の境界和の全添字の対応

概要：左右の切断削除の添字は、削除後の切断と二種類の対角添字に分かれる。
方針：削除点と切断点の大小と等号で明示的な同値を作る。
規約：対角は左から消す場合と右から消す場合を別々に残す。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の AW 微分の和を標準境界へ移す。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

variable {α : Type*} [LinearOrder α] (J : Finset α)

/-- 概要：左右の削除添字を非対角と二つの対角へ分ける。
方針：削除点と切断点が等しいかで場合分けする。
規約：非対角の添字では削除点を先に置く。
使われ方：Kerodon 2.5.8（Tag 00S0） の境界和の添字の移送。 -/
def boundaryPairMap :
    ((Σ i : J, ↥(J.filter (· ≤ i.val))) ⊕ (Σ i : J, ↥(J.filter (i.val ≤ ·)))) →
      (Σ j : J, ↥(J.erase j.val)) ⊕ (J ⊕ J)
  | .inl ⟨i, j⟩ =>
      if he : j.val = i.val then .inr (.inl i)
      else .inl ⟨⟨j.val, (Finset.mem_filter.mp j.property).1⟩,
        ⟨i.val, Finset.mem_erase.mpr ⟨Ne.symm he, i.property⟩⟩⟩
  | .inr ⟨i, j⟩ =>
      if he : j.val = i.val then .inr (.inr i)
      else .inl ⟨⟨j.val, (Finset.mem_filter.mp j.property).1⟩,
        ⟨i.val, Finset.mem_erase.mpr ⟨Ne.symm he, i.property⟩⟩⟩

/-- 概要：削除後の切断または対角添字から元の左右の削除添字へ戻す。
方針：非対角では削除点と切断点の大小を比較する。
規約：二種類の対角は元の側へ戻す。
使われ方：Kerodon 2.5.8（Tag 00S0） の境界和の添字の逆写像。 -/
def boundaryPairInv :
    (Σ j : J, ↥(J.erase j.val)) ⊕ (J ⊕ J) →
      ((Σ i : J, ↥(J.filter (· ≤ i.val))) ⊕ (Σ i : J, ↥(J.filter (i.val ≤ ·))))
  | .inl ⟨j, i⟩ =>
      if hj : j.val < i.val then .inl
        ⟨⟨i.val, (Finset.mem_erase.mp i.property).2⟩,
          ⟨j.val, Finset.mem_filter.mpr ⟨j.property, hj.le⟩⟩⟩
      else .inr ⟨⟨i.val, (Finset.mem_erase.mp i.property).2⟩,
        ⟨j.val, Finset.mem_filter.mpr ⟨j.property, le_of_not_gt hj⟩⟩⟩
  | .inr (.inl i) => .inl ⟨i, ⟨i.val, Finset.mem_filter.mpr ⟨i.property, le_rfl⟩⟩⟩
  | .inr (.inr i) => .inr ⟨i, ⟨i.val, Finset.mem_filter.mpr ⟨i.property, le_rfl⟩⟩⟩

/-- 概要：左右の切断削除と、削除後の切断および二つの対角の型は同値である。
方針：削除点が切断点より左・右・等しい場合に分けて逆写像を作る。
規約：空集合と一点集合も同じ型の同値で扱う。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW 境界の和の全添字の移送。 -/
def boundaryPairEquiv :
    ((Σ i : J, ↥(J.filter (· ≤ i.val))) ⊕ (Σ i : J, ↥(J.filter (i.val ≤ ·)))) ≃
      (Σ j : J, ↥(J.erase j.val)) ⊕ (J ⊕ J) where
  toFun := boundaryPairMap J
  invFun := boundaryPairInv J
  left_inv := by
    intro p
    rcases p with ⟨i, j⟩ | ⟨i, j⟩
    · by_cases he : j.val = i.val
      · have hj : j = ⟨i.val, Finset.mem_filter.mpr ⟨i.property, le_rfl⟩⟩ := Subtype.ext he
        subst j
        simp [boundaryPairMap, boundaryPairInv]
      · have hj : j.val < i.val := lt_of_le_of_ne (Finset.mem_filter.mp j.property).2 he
        simp [boundaryPairMap, boundaryPairInv, he, hj]
    · by_cases he : j.val = i.val
      · have hj : j = ⟨i.val, Finset.mem_filter.mpr ⟨i.property, le_rfl⟩⟩ := Subtype.ext he
        subst j
        simp [boundaryPairMap, boundaryPairInv]
      · have hj : ¬j.val < i.val := not_lt_of_ge (Finset.mem_filter.mp j.property).2
        simp [boundaryPairMap, boundaryPairInv, he, hj]
  right_inv := by
    intro p
    rcases p with ⟨j, i⟩ | (i | i)
    · have he : j.val ≠ i.val := (Finset.mem_erase.mp i.property).1.symm
      by_cases hj : j.val < i.val
      · simp [boundaryPairMap, boundaryPairInv, he, hj]
      · simp [boundaryPairMap, boundaryPairInv, he, hj]
    · simp [boundaryPairMap, boundaryPairInv]
    · simp [boundaryPairMap, boundaryPairInv]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

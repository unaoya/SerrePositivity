module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWUnit

/-!
# AW の二重切断の和の交換

概要：順序付けられた二つの切断点の和は先の点と後の点のどちらから足しても一致する。
方針：切断点の依存対の型の明示的な同値で二重和を移す。
規約：切断点が等しい場合を含む。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の AW 結合律。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

variable {α : Type*} [LinearOrder α] (J : Finset α)

/-- 概要：先の切断点から選ぶ二切断と後の切断点から選ぶ二切断は同値である。
方針：二つの点を交換し、所属条件を filter の条件へ移す。
規約：各点は元の有限集合に属する。
使われ方：Kerodon 2.5.8（Tag 00S0） の二重和の交換の添字の同値。 -/
def cutPairEquiv :
    (Σ i : J, ↥(J.filter (i.val ≤ ·))) ≃ (Σ j : J, ↥(J.filter (· ≤ j.val))) where
  toFun p := ⟨⟨p.2.val, (Finset.mem_filter.mp p.2.property).1⟩,
    ⟨p.1.val, Finset.mem_filter.mpr ⟨p.1.property, (Finset.mem_filter.mp p.2.property).2⟩⟩⟩
  invFun p := ⟨⟨p.2.val, (Finset.mem_filter.mp p.2.property).1⟩,
    ⟨p.1.val, Finset.mem_filter.mpr ⟨p.1.property, (Finset.mem_filter.mp p.2.property).2⟩⟩⟩
  left_inv p := by rcases p with ⟨i, j⟩; rfl
  right_inv p := by rcases p with ⟨j, i⟩; rfl

/-- 概要：順序付けられた二切断に沿う和は二つの切断点の足す順序を交換できる。
方針：二重和を依存対上の和にし、切断点の同値を適用する。
規約：値は任意の可換加法モノイドでよい。
使われ方：HA 1.3.1.13 の AW の結合律の和の交換。 -/
lemma sum_rightCuts_eq_leftCuts {M : Type*} [AddCommMonoid M]
    (F : (i j : J) → i.val ≤ j.val → M) :
    (∑ i : J, ∑ j : J.filter (i.val ≤ ·),
      F i ⟨j.val, (Finset.mem_filter.mp j.property).1⟩
        (Finset.mem_filter.mp j.property).2) =
      ∑ j : J, ∑ i : J.filter (· ≤ j.val),
        F ⟨i.val, (Finset.mem_filter.mp i.property).1⟩ j
          (Finset.mem_filter.mp i.property).2 := by
  let L : (Σ i : J, ↥(J.filter (i.val ≤ ·))) → M := fun p ↦
    F p.1 ⟨p.2.val, (Finset.mem_filter.mp p.2.property).1⟩
      (Finset.mem_filter.mp p.2.property).2
  let G : (Σ j : J, ↥(J.filter (· ≤ j.val))) → M := fun p ↦
    F ⟨p.2.val, (Finset.mem_filter.mp p.2.property).1⟩ p.1
      (Finset.mem_filter.mp p.2.property).2
  change (∑ i : J, ∑ j : J.filter (i.val ≤ ·), L ⟨i, j⟩) =
    ∑ j : J, ∑ i : J.filter (· ≤ j.val), G ⟨j, i⟩
  rw [← Fintype.sum_sigma L, ← Fintype.sum_sigma G]
  apply Fintype.sum_equiv (cutPairEquiv J)
  intro p
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

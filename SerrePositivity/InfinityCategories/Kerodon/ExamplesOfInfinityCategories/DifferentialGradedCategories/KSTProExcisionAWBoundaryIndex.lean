module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AlexanderWhitney

/-!
# AW の非対角境界項の添字

概要：前半と後半の内部境界の添字を、全単体の削除点と削除後の切断点に対応させる。
方針：削除点が切断点以前なら前半、その後なら後半に戻す明示的な同値を作る。
規約：KST Construction A.5 の標準 AW。切断点自体の二つの境界項は別に相殺する。
使われ方：AW の鎖写像性における二重境界和の添字変換。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：前半の境界の切断点以外の削除項の添字。
方針：切断点 i と削除点 k<i の対にする。
規約：KST A.5、全次数は n+1。使われ方：左の非対角境界和。 -/
abbrev AWLeftIndex (n : ℕ) := {p : Fin (n + 2) × Fin (n + 2) // p.2 < p.1}

/-- 概要：後半の境界の切断点以外の削除項の添字。
方針：切断点 i と後半内の削除点 0<k、i+k≤n+1 の対にする。
規約：KST A.5、局所削除点を用いる。使われ方：右の非対角境界和。 -/
abbrev AWRightIndex (n : ℕ) :=
  {p : Fin (n + 2) × Fin (n + 2) // 0 < (p.2 : ℕ) ∧ (p.1 : ℕ) + p.2 ≤ n + 1}

/-- 概要：左右の非対角境界から削除点と削除後の切断点への写像。
方針：前半では切断点を一つ減らし、後半では局所削除点に切断点を足す。
規約：KST A.5、両側を非交和に分ける。
使われ方：境界和の添字の同値の順方向。 -/
def awBoundaryIndexForward (n : ℕ) :
    AWLeftIndex n ⊕ AWRightIndex n → Fin (n + 2) × Fin (n + 1)
  | .inl ⟨⟨i, k⟩, h⟩ => (k, ⟨(i : ℕ) - 1, by have := i.isLt; have := k.isLt; omega⟩)
  | .inr ⟨⟨i, k⟩, h⟩ =>
      (⟨(i : ℕ) + k, by
        have h' : 0 < (k : ℕ) ∧ (i : ℕ) + k ≤ n + 1 := h
        omega⟩, ⟨i, by
        have h' : 0 < (k : ℕ) ∧ (i : ℕ) + k ≤ n + 1 := h
        omega⟩)

/-- 概要：削除点と削除後の切断点から左右の非対角境界への写像。
方針：削除点 k≤p なら前半の切断点 p+1、そうでなければ後半の局所点 k−p。
規約：KST A.5。使われ方：境界和の添字の同値の逆方向。 -/
def awBoundaryIndexInverse (n : ℕ) (p : Fin (n + 2) × Fin (n + 1)) :
    AWLeftIndex n ⊕ AWRightIndex n :=
  if h : (p.1 : ℕ) ≤ p.2 then
    .inl ⟨(⟨(p.2 : ℕ) + 1, by have := p.2.isLt; omega⟩, p.1), by
      change (p.1 : ℕ) < (p.2 : ℕ) + 1
      omega⟩
  else
    .inr ⟨(⟨p.2, by have := p.2.isLt; omega⟩,
      ⟨(p.1 : ℕ) - p.2, by have := p.1.isLt; omega⟩), by
        change 0 < (p.1 : ℕ) - p.2 ∧ (p.2 : ℕ) + ((p.1 : ℕ) - p.2) ≤ n + 1
        have := p.1.isLt
        omega⟩

/-- 概要：AW の非対角境界の添字と削除後の切断の添字は同値。
方針：削除点と切断点の大小の二分を使い、両逆の頂点番号を計算する。
規約：KST A.5、追加の数学的仮定を使わない。
使われ方：左右の非対角境界和を、先に頂点を削除してから AW を取る和へ移す。 -/
def awBoundaryIndexEquiv (n : ℕ) :
    AWLeftIndex n ⊕ AWRightIndex n ≃ Fin (n + 2) × Fin (n + 1) where
  toFun := awBoundaryIndexForward n
  invFun := awBoundaryIndexInverse n
  left_inv p := by
    rcases p with ⟨⟨i, k⟩, h⟩ | ⟨⟨i, k⟩, h⟩
    · change (k : ℕ) < (i : ℕ) at h
      have hi := i.isLt
      have hk := k.isLt
      dsimp only [awBoundaryIndexForward, awBoundaryIndexInverse]
      split_ifs with hki
      · apply congrArg Sum.inl
        apply Subtype.ext
        apply Prod.ext
        · apply Fin.ext
          dsimp
          omega
        · rfl
      · omega
    · change 0 < (k : ℕ) ∧ (i : ℕ) + k ≤ n + 1 at h
      have hi := i.isLt
      have hk := k.isLt
      dsimp only [awBoundaryIndexForward, awBoundaryIndexInverse]
      split_ifs with hki
      · omega
      · apply congrArg Sum.inr
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Fin.ext
          dsimp
          omega
  right_inv p := by
    rcases p with ⟨k, i⟩
    have hi := i.isLt
    have hk := k.isLt
    dsimp only [awBoundaryIndexInverse]
    split_ifs with h
    all_goals
      ext <;> dsimp [awBoundaryIndexForward] <;> omega

/-- 概要：左右の非対角境界和を削除点と削除後の切断点の二重和へ移す。
方針：明示的な添字の同値に沿って有限和を移す。
規約：KST A.5、任意の可換加法モノイドに成立。
使われ方：AW の鎖写像性の境界和の整理。 -/
lemma awBoundaryIndex_sum {A : Type*} [AddCommMonoid A] (n : ℕ)
    (F : Fin (n + 2) × Fin (n + 1) → A) :
    (∑ x : AWLeftIndex n, F (awBoundaryIndexForward n (.inl x))) +
      (∑ x : AWRightIndex n, F (awBoundaryIndexForward n (.inr x))) =
        ∑ k : Fin (n + 2), ∑ i : Fin (n + 1), F (k, i) := by
  have h := Fintype.sum_equiv (awBoundaryIndexEquiv n)
    (fun x ↦ F (awBoundaryIndexForward n x)) F (fun _ ↦ rfl)
  simpa only [Fintype.sum_sum_type, Fintype.sum_prod_type] using h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories


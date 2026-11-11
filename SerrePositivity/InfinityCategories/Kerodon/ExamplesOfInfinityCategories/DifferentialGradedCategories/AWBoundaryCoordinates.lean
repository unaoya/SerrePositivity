module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.KSTProExcisionAWBoundaryIndex

/-!
# 実境界和と AW の境界添字の座標

概要：水平境界と垂直境界の入れ子の有限和の添字を、非対角境界の添字へ同定する。
方針：水平側は切断点を一つ増やし、垂直側は局所削除点を一つ増やす。
規約：KST Construction A.5 の標準 AW。全次数 n+1 の境界を扱う。
使われ方：実際の水平・垂直微分の展開へ awBoundaryIndex_sum を適用する。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：水平側の入れ子の非対角境界添字を全体の切断点と削除点へ移す。
方針：i を i+1、k をそのまま全単体の番号とする。
規約：KST A.5、k<i+1。使われ方：水平境界の二重和の添字変換。 -/
def awLeftBoundaryCoordinates (n : ℕ) :
    (Σ i : Fin (n + 1), Fin ((i : ℕ) + 1)) ≃ AWLeftIndex n where
  toFun p := ⟨(p.1.succ, ⟨p.2, by have := p.1.isLt; have := p.2.isLt; omega⟩), p.2.isLt⟩
  invFun p :=
    ⟨⟨(p.val.1 : ℕ) - 1, by
        have := p.val.1.isLt
        have h : (p.val.2 : ℕ) < p.val.1 := p.property
        omega⟩,
      ⟨p.val.2, by
        change (p.val.2 : ℕ) < (p.val.1 : ℕ) - 1 + 1
        have h : (p.val.2 : ℕ) < p.val.1 := p.property
        omega⟩⟩
  left_inv p := by
    rcases p with ⟨i, k⟩
    have he : (⟨((i : ℕ) + 1) - 1, by have := i.isLt; omega⟩ : Fin (n + 1)) = i := by
      apply Fin.ext
      simp
    apply Sigma.ext he
    apply (Fin.heq_ext_iff (congrArg (fun i : Fin (n + 1) ↦ (i : ℕ) + 1) he)).mpr
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      dsimp
      have h : (p.val.2 : ℕ) < p.val.1 := p.property
      omega
    · rfl

/-- 概要：垂直側の入れ子の非対角境界添字を全体の切断点と局所削除点へ移す。
方針：i をそのまま、k を k+1 として最初の面を除く。
規約：KST A.5、0<k+1≤n+1−i。使われ方：垂直境界の二重和の添字変換。 -/
def awRightBoundaryCoordinates (n : ℕ) :
    (Σ i : Fin (n + 1), Fin (n - (i : ℕ) + 1)) ≃ AWRightIndex n where
  toFun p := ⟨(p.1.castSucc, ⟨(p.2 : ℕ) + 1, by
      have hi := p.1.isLt
      have hk := p.2.isLt
      omega⟩), by
        change 0 < (p.2 : ℕ) + 1 ∧ (p.1 : ℕ) + ((p.2 : ℕ) + 1) ≤ n + 1
        have hi := p.1.isLt
        have hk := p.2.isLt
        omega⟩
  invFun p :=
    ⟨⟨p.val.1, by
        have h : 0 < (p.val.2 : ℕ) ∧ (p.val.1 : ℕ) + p.val.2 ≤ n + 1 := p.property
        omega⟩,
      ⟨(p.val.2 : ℕ) - 1, by
        change (p.val.2 : ℕ) - 1 < n - (p.val.1 : ℕ) + 1
        have h : 0 < (p.val.2 : ℕ) ∧ (p.val.1 : ℕ) + p.val.2 ≤ n + 1 := p.property
        omega⟩⟩
  left_inv p := by
    rcases p with ⟨i, k⟩
    apply Sigma.ext (Fin.eta i _)
    apply (Fin.heq_ext_iff rfl).mpr
    change (k : ℕ) + 1 - 1 = (k : ℕ)
    omega
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      dsimp
      have h : 0 < (p.val.2 : ℕ) ∧ (p.val.1 : ℕ) + p.val.2 ≤ n + 1 := p.property
      omega

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

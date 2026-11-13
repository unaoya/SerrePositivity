module

public import SerrePositivity.EInfinity.SimplexCuts.HomogeneousTensor
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# 切断の境界項の面と次数移送

Berger–Fresse §2.2.6–7。出力の一面を削除するときの標準面写像と、
総次数が一だけ下がる計算を保持する（M14 L09a 前提計算2）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- 正次数の単体の標準面。空の境界は別に零として扱う。 -/
def boundaryFace : (k : ℕ) → 0 < k → Fin (k + 1) →
    ((⦋k - 1⦌ : SimplexCategory) ⟶ ⦋k⦌)
  | 0, h, _ => False.elim (Nat.not_lt_zero _ h)
  | k + 1, _, i => SimplexCategory.δ (n := k) i

/-- 同じ斉次テンソルの一因子の次数を下げると、全次数も一だけ下がる。 -/
lemma degreeSum_delete {n : ℕ} (d : Fin n → ℕ) (i : Fin n) (h : 0 < d i) :
    degreeSum n (Function.update d i (d i - 1)) + 1 = degreeSum n d := by
  rw [degreeSum_eq_sum, degreeSum_eq_sum]
  have h₁ := Finset.sum_update_of_mem (s := Finset.univ) (Finset.mem_univ i) d (d i - 1)
  have h₂ := Finset.sum_update_of_mem (s := Finset.univ) (Finset.mem_univ i) d (d i)
  rw [Function.update_eq_self] at h₂
  rw [h₁, h₂]
  omega

end SerrePositivity.EInfinity.SimplexCuts

module

public import SerrePositivity.CommutativeAlgebra.RootTower.Basic
public import Mathlib.Basic.ENNReal.Inv

/-! # 根の指数と段の階数を保った正規化の計算

二つの段の差の倍率と根の指数の倍率を、dim(A)=r+2の段階数で割る。
有限段mが根の指数nより大きくても、結果はc/p^nとなる。
-/

@[expose] public section
namespace SerrePositivity.RootTowerLength
open Section2
open scoped ENNReal

/-- 三つの倍率と有限段の階数の正規化。零や無限大による除算は使わない。 -/
theorem root_stage_normalization (p : ℕ) (hp : p ≠ 0) (r n m : ℕ) (hnm : n ≤ m)
    (c : ℝ≥0∞) :
    (p : ℝ≥0∞) ^ n *
      (((p : ℝ≥0∞) ^ (m - n) *
        ((p : ℝ≥0∞) ^ (m - n) * (((p : ℝ≥0∞) ^ m) ^ r * c))) /
          (stageRank (r + 2) p m : ℝ≥0∞)) = c / (p : ℝ≥0∞) ^ n := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp
  have hrank : (stageRank (r + 2) p m : ℝ≥0∞) = (p : ℝ≥0∞) ^ (m * (r + 2)) := by
    simp only [stageRank, Nat.cast_pow]
  rw [hrank, ← mul_div_assoc]
  apply (ENNReal.div_eq_div_iff (pow_ne_zero _ hp0) (by simp)
    (pow_ne_zero _ hp0) (by simp)).mpr
  simp only [← pow_mul]
  have hexp : n + (m - n) + (m - n) + m * r + n = m * (r + 2) := by
    simp only [Nat.mul_add, Nat.mul_two]
    omega
  calc
    _ = (p : ℝ≥0∞) ^ (n + (m - n) + (m - n) + m * r + n) * c := by
      simp only [pow_add]
      ac_rfl
    _ = _ := by rw [hexp]

end SerrePositivity.RootTowerLength

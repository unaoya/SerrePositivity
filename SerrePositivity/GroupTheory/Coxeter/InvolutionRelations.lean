module

public import Mathlib.GroupTheory.Coxeter.Basic

/-!
# 対合から Coxeter 関係への比較

対合二つの braid 関係と可換性から、積の三乗・二乗の関係を得る。
圏やスペクトルに依存しない群論。
-/

@[expose] public section

namespace SerrePositivity.Coxeter

/-- 対合二つの braid 関係から積の三乗が恒等となる。 -/
lemma involution_pair_cube {G : Type*} [Group G] (a b : G)
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b * a = b * a * b) :
    (a * b) ^ 3 = 1 := by
  calc
    (a * b) ^ 3 = (a * b * a) * b * a * b := by simp [pow_succ, mul_assoc]
    _ = (b * a * b) * b * a * b := by rw [hab]
    _ = b * a * (b * b) * a * b := by simp [mul_assoc]
    _ = b * (a * a) * b := by rw [hb]; simp [mul_assoc]
    _ = 1 := by rw [ha]; simp [hb]

/-- 可換な対合二つの積の二乗は恒等となる。 -/
lemma involution_pair_square {G : Type*} [Group G] (a b : G)
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    (a * b) ^ 2 = 1 := by
  calc
    (a * b) ^ 2 = a * (b * a) * b := by simp [pow_two, mul_assoc]
    _ = a * (a * b) * b := by rw [← hab]
    _ = (a * a) * (b * b) := by simp [mul_assoc]
    _ = 1 := by rw [ha, hb]; simp

end SerrePositivity.Coxeter

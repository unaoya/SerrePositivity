module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# 主開局所化条件の同型による移送

## 概要
基底と局所化環の可換な同型の正方形は主開局所化条件を保つ。

## 方針
単元性・分数表示・等式を消す分母の三条件を同型で移す。

## 規約
環の同型の正方形だけを要求し、代数構造の定義的な一致には依存しない。

## 使われ方
Stacks 00CM。結晶 Zariski 被覆を小さい模型の同値で移す補題。
-/

public section
universe u
namespace SerrePositivity.CommutativeAlgebra.Localization
variable {B B' T T' : Type u} [CommRing B] [CommRing B'] [CommRing T] [CommRing T']
variable [Algebra B T] [Algebra B' T']

/-- 同型の可換正方形による主開局所化条件の移送。 -/
theorem away_of_equivalence (e : B ≃+* B') (v : T ≃+* T')
    (he : ∀ b, v (algebraMap B T b) = algebraMap B' T' (e b))
    (b : B) [IsLocalization.Away b T] : IsLocalization.Away (e b) T' := by
  apply IsLocalization.Away.mk
  · rw [← he b]
    exact (IsLocalization.Away.algebraMap_isUnit b).map v
  · intro z
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj b (v.symm z)
    refine ⟨n, e a, ?_⟩
    have h := congrArg v ha
    simpa only [map_mul, map_pow, v.apply_symm_apply, he] using h
  · intro x y hxy
    have h : algebraMap B T (e.symm x) = algebraMap B T (e.symm y) := by
      apply v.injective
      simpa only [he, e.apply_symm_apply] using hxy
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq b h
    refine ⟨n, ?_⟩
    simpa only [map_mul, map_pow, e.apply_symm_apply] using congrArg e hn

end SerrePositivity.CommutativeAlgebra.Localization

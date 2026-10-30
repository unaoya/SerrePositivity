module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Shift.Linear

/-! # 線形圏のスカラー恒等射の冪零性

## 概要

R 線形な圏でのスカラー恒等射 `a • 𝟙 X` についての小さな補題を二つ置く。完全三角形 `X → Y → Z → X[1]` で
`a • 𝟙 Y` と `(a • 𝟙 X)[1]` が三角形の射と合成して零になるなら `a² • 𝟙 Z = 0`（`smul_mul_self_id_eq_zero`）、
`a^v • 𝟙 X = 0` なら `v ≤ w` で `a^w • 𝟙 X = 0`（`pow_smul_id_eq_zero_of_le`）。

## 方針

前者は Mathlib の `Triangle.yoneda_exact₃` で `a • 𝟙 Z` を三角形の射の経由に分解する。後者は冪の分解だけ。

## 規約

Mathlib だけを import する軽いファイル。以前は HomologicalAlgebra/NullHomotopy にあったが、CategoryTheory の
ScalarSupport が使うので層の順序に合わせて下ろした。

## 使われ方

スカラー支持（`ScalarSupport`）、零ホモトピー（HomologicalAlgebra/NullHomotopy）、PerfectComplex/Support、Asymptotic・
IntersectionMultiplicity の Koszul の評価。
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

section triangle

variable {R : Type*} [Ring R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
  [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [(shiftFunctor C (1 : ℤ)).Linear R]

/-- 完全三角形 `T = (X →f Y →g Z →h X[1])` とスカラー `a` について、`a • 𝟙 Y` のあとに `g` を
合成すると零（`h₂`）、`h` のあとに `(a • 𝟙 X)[1]` を合成すると零（`h₃`）なら、`a² • 𝟙 Z = 0`。

`u := a • 𝟙 Z` とおくと、仮定は `g ≫ u = 0` と `u ≫ h = 0` に言い換えられる。完全三角形では
`g ≫ u = 0` となる射 `u` は `h` を経由する、すなわち `u = h ≫ v` となる `v : X[1] ⟶ Z` がある
（Mathlib の `Triangle.yoneda_exact₃`）。すると `u ≫ u = u ≫ h ≫ v = 0 ≫ v = 0` である。
`a² • 𝟙 Z = u ≫ u` なので結論が従う。`R` 線形な一般の三角圏で成り立つ。 -/
lemma smul_mul_self_id_eq_zero (T : Triangle C) (hT : T ∈ distTriang C) (a : R)
    (h₂ : (a • 𝟙 T.obj₂) ≫ T.mor₂ = 0)
    (h₃ : T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map (a • 𝟙 T.obj₁) = 0) :
    (a * a) • 𝟙 T.obj₃ = 0 := by
  set u : T.obj₃ ⟶ T.obj₃ := a • 𝟙 T.obj₃
  have hu₂ : T.mor₂ ≫ u = 0 := by
    rw [Linear.comp_smul, Category.comp_id, ← h₂, Linear.smul_comp, Category.id_comp]
  have hu₃ : u ≫ T.mor₃ = 0 := by
    rw [← h₃, Linear.smul_comp, Category.id_comp, Functor.map_smul, CategoryTheory.Functor.map_id,
      Linear.comp_smul, Category.comp_id]
  obtain ⟨v, hv⟩ := Triangle.yoneda_exact₃ T hT u hu₂
  have : (a * a) • 𝟙 T.obj₃ = u ≫ u := by
    rw [mul_smul, Linear.smul_comp, Category.id_comp]
  rw [this]
  calc u ≫ u = u ≫ (T.mor₃ ≫ v) := by rw [← hv]
    _ = 0 := by rw [← Category.assoc, hu₃, zero_comp]

end triangle

section power

variable {R : Type*} [CommRing R]

/-- `a^v • 𝟙 X = 0` なら、`v ≤ w` となるすべての `w` で `a^w • 𝟙 X = 0`。`a^w = a^{w-v} · a^v` と
分けるだけ。複数の生成元 `z_j` についてそれぞれ冪 `v_j` がとれたとき、それらの最大値を共通の冪に
とるのに使う（`PerfectComplex/Support.lean` の `isSupported_of_forall`）。 -/
lemma pow_smul_id_eq_zero_of_le {C : Type*} [Category C] [Preadditive C] [Linear R C] {X : C}
    {a : R} {v w : ℕ} (h : a ^ v • 𝟙 X = 0) (hvw : v ≤ w) : a ^ w • 𝟙 X = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hvw
  rw [pow_add, mul_comm, mul_smul, h, smul_zero]

end power

end SerrePositivity

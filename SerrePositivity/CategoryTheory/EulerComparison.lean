module

public import SerrePositivity.CategoryTheory.HomologicalEuler
public import SerrePositivity.GroupTheory.ConjugateSum

/-! # 二つのホモロジー的 Euler 評価の対称な比較

評価先のアーベル圏は異なってよい。群は評価元の Grothendieck 群に作用する。
評価関手の同変性や長さの群不変性は使わない。

- `homologicalEulerK0_conjSum_eq`：同じ三角圏上の二つの Euler 評価について、基底から来る類での一致と
  不変類の降下から共役和が一致する（解説の命題「Euler 評価の共役和比較」）。
- `homologicalEulerK0_pullback_conjSum_eq_of_base_formula`：二つの実現で使う形。評価元 `C` の `K₀` に群が
  作用し、二つの評価はそれぞれ別の三角圏 `C₁`、`C₂` 上の Euler 評価を準同型 `u₁`、`u₂`（係数変更が
  誘導する写像）で引き戻したもの。基底から来る類での評価が、基底上の共通の評価 `χA` の定数倍
  `e₁ * χA`、`e₂ * χA` になること（基底公式）と `e₁ = e₂`、降下から共役和が一致する
  （解説の系「基底公式つきの共役和比較」）。perfect 複体版（`LengthAlgebra/Comparison`）と
  ランク無視版（`Paper/Section4/SymmetricComparison`）はこの定理の適用である。
-/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
  (l₁ : A → ℝ)
  (hi₁ : ∀ {X Y : A}, (X ≅ Y) → l₁ X = l₁ Y)
  (ha₁ : ∀ {S : ShortComplex A}, S.ShortExact → l₁ S.X₂ = l₁ S.X₁ + l₁ S.X₃)
  (hz₁ : ∀ X, IsZero X → l₁ X = 0)
  (l₂ : B → ℝ)
  (hi₂ : ∀ {X Y : B}, (X ≅ Y) → l₂ X = l₂ Y)
  (ha₂ : ∀ {S : ShortComplex B}, S.ShortExact → l₂ S.X₂ = l₂ S.X₁ + l₂ S.X₃)
  (hz₂ : ∀ X, IsZero X → l₂ X = 0)

section SameCategory

variable (F₁ : C ⥤ A) [F₁.IsHomological] [F₁.ShiftSequence ℤ]
  (hb₁ : ∀ X : C, ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((F₁.shift q).obj X))
  (F₂ : C ⥤ B) [F₂.IsHomological] [F₂.ShiftSequence ℤ]
  (hb₂ : ∀ X : C, ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((F₂.shift q).obj X))

/-- 基底からの一致と不変類の降下による、二つの Euler 評価の共役和の一致。 -/
theorem homologicalEulerK0_conjSum_eq
    {K : Type*} [AddCommGroup K] (f : K →+ TriangulatedK0 C)
    {G : Type*} [Group G] [Fintype G] [DistribMulAction G (TriangulatedK0 C)]
    (hbase : ∀ x,
      homologicalEulerK0 l₁ hi₁ ha₁ F₁ hz₁ hb₁ (f x) =
        homologicalEulerK0 l₂ hi₂ ha₂ F₂ hz₂ hb₂ (f x))
    (hdesc : ∀ y : TriangulatedK0 C, (∀ g : G, g • y = y) →
      ∃ (n : ℕ) (x : K), 0 < n ∧ n • y = f x)
    (y : TriangulatedK0 C) :
    ∑ g : G, homologicalEulerK0 l₁ hi₁ ha₁ F₁ hz₁ hb₁ (g • y) =
      ∑ g : G, homologicalEulerK0 l₂ hi₂ ha₂ F₂ hz₂ hb₂ (g • y) :=
  conjSum_eq f _ _ hbase hdesc y

end SameCategory

section Pullback

variable {C₁ : Type*} [Category* C₁] [Preadditive C₁] [HasZeroObject C₁] [HasShift C₁ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [Pretriangulated C₁]
  {C₂ : Type*} [Category* C₂] [Preadditive C₂] [HasZeroObject C₂] [HasShift C₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₂ n).Additive] [Pretriangulated C₂]
  (F₁ : C₁ ⥤ A) [F₁.IsHomological] [F₁.ShiftSequence ℤ]
  (hb₁ : ∀ X : C₁, ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((F₁.shift q).obj X))
  (F₂ : C₂ ⥤ B) [F₂.IsHomological] [F₂.ShiftSequence ℤ]
  (hb₂ : ∀ X : C₂, ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((F₂.shift q).obj X))

/-- **基底公式つきの共役和比較（引き戻した Euler 評価）**：評価元 `C` の `K₀` に有限群 `G` が作用し、
二つの評価 `χᵢ = (C_i 上の Euler 評価) ∘ uᵢ` が、基底 `K` からの写像 `f` に沿って共通の `χA` の定数倍
`eᵢ * χA` に等しい（基底公式）とする。`e₁ = e₂` と不変類の降下から、全ての類で共役和が一致する。
評価先 `A`、`B` を同じ圏に同定する必要も、`uᵢ` の同変性も要らない。 -/
theorem homologicalEulerK0_pullback_conjSum_eq_of_base_formula
    (u₁ : TriangulatedK0 C →+ TriangulatedK0 C₁) (u₂ : TriangulatedK0 C →+ TriangulatedK0 C₂)
    {K : Type*} [AddCommGroup K] (f : K →+ TriangulatedK0 C)
    {G : Type*} [Group G] [Fintype G] [DistribMulAction G (TriangulatedK0 C)]
    (χA : K → ℝ) (e₁ e₂ : ℝ)
    (h₁ : ∀ x, ((homologicalEulerK0 l₁ hi₁ ha₁ F₁ hz₁ hb₁).comp u₁) (f x) = e₁ * χA x)
    (h₂ : ∀ x, ((homologicalEulerK0 l₂ hi₂ ha₂ F₂ hz₂ hb₂).comp u₂) (f x) = e₂ * χA x)
    (he : e₁ = e₂)
    (hdesc : ∀ y : TriangulatedK0 C, (∀ g : G, g • y = y) →
      ∃ (n : ℕ) (x : K), 0 < n ∧ n • y = f x)
    (y : TriangulatedK0 C) :
    ∑ g : G, ((homologicalEulerK0 l₁ hi₁ ha₁ F₁ hz₁ hb₁).comp u₁) (g • y) =
      ∑ g : G, ((homologicalEulerK0 l₂ hi₂ ha₂ F₂ hz₂ hb₂).comp u₂) (g • y) :=
  conjSum_eq_of_base_formula f _ _ χA e₁ e₂ h₁ h₂ he hdesc y

end Pullback

end SerrePositivity

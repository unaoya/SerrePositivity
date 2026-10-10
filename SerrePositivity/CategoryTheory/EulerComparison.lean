module

public import SerrePositivity.CategoryTheory.HomologicalEuler
public import SerrePositivity.GroupTheory.ConjugateSum

/-! # 二つのホモロジー的 Euler 評価の対称な比較

評価先のアーベル圏は異なってよい。群は評価元の Grothendieck 群に作用する。
評価関手の同変性や長さの群不変性は使わない。
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
  (F₁ : C ⥤ A) [F₁.IsHomological] [F₁.ShiftSequence ℤ]
  (hz₁ : ∀ X, IsZero X → l₁ X = 0)
  (hb₁ : ∀ X : C, ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((F₁.shift q).obj X))
  (l₂ : B → ℝ)
  (hi₂ : ∀ {X Y : B}, (X ≅ Y) → l₂ X = l₂ Y)
  (ha₂ : ∀ {S : ShortComplex B}, S.ShortExact → l₂ S.X₂ = l₂ S.X₁ + l₂ S.X₃)
  (F₂ : C ⥤ B) [F₂.IsHomological] [F₂.ShiftSequence ℤ]
  (hz₂ : ∀ X, IsZero X → l₂ X = 0)
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

end SerrePositivity

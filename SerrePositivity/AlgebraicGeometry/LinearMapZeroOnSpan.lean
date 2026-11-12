module

public import Mathlib.LinearAlgebra.Span.Basic

/-!
概要：別の係数環上の生成元とそのスカラー倍で、線形写像の零化を判定する。
方針：任意のスカラー倍が零になるという述語で、生成部分加群について帰納する。
規約：終域には生成に使う環の加群構造を要求しない。
使われ方：Rees 環上の斉次生成元から、R 線形な Čech 遷移の零化を得る。
-/

@[expose] public section
namespace SerrePositivity.AlgebraicGeometry

/-- 生成元のすべての B 倍で零なら、R 線形写像はその B 生成部分加群で零。 -/
theorem linearMap_zero_on_span_of_smul_generators
    {R B E N : Type*} [Semiring R] [Semiring B]
    [AddCommMonoid E] [Module R E] [Module B E]
    [AddCommMonoid N] [Module R N]
    (f : E →ₗ[R] N) (s : Set E)
    (hs : ∀ x ∈ s, ∀ b : B, f (b • x) = 0)
    (x : E) (hx : x ∈ Submodule.span B s) : f x = 0 := by
  have h : ∀ b : B, f (b • x) = 0 := by
    induction hx using Submodule.span_induction with
    | mem y hy => exact hs y hy
    | zero => intro b; simp only [smul_zero, map_zero]
    | add y z hy hz ihy ihz =>
      intro b
      simp only [smul_add, map_add, ihy b, ihz b, add_zero]
    | smul a y hy ih =>
      intro b
      rw [smul_smul]
      exact ih (b * a)
  simpa only [one_smul] using h 1

end SerrePositivity.AlgebraicGeometry

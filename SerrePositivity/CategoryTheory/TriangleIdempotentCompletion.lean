module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Tactic.NoncommRing

/-! # 完全三角形の二つの冪等元を第三の冪等元へ延長する -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

/-- 冪等性の誤差の二乗が零なら、三次多項式で冪等元に補正できる。 -/
lemma idempotent_cubic {R : Type*} [Ring R] (x : R)
    (h : (x * x - x) * (x * x - x) = 0) :
    (3 * (x * x) - 2 * (x * x * x)) * (3 * (x * x) - 2 * (x * x * x)) =
      3 * (x * x) - 2 * (x * x * x) := by
  apply sub_eq_zero.mp
  calc
    _ = (4 * (x * x) - 4 * x - 3) * ((x * x - x) * (x * x - x)) := by noncomm_ring
    _ = 0 := by rw [h, mul_zero]

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- 第一・第二成分が零の三角形自己射の第三成分は二乗零。 -/
lemma triangle_end_square_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (c : T.obj₃ ⟶ T.obj₃) (hg : T.mor₂ ≫ c = 0) (hh : c ≫ T.mor₃ = 0) :
    c ≫ c = 0 := by
  obtain ⟨a, ha⟩ := T.yoneda_exact₃ hT c hg
  conv_lhs => rhs; rw [ha]
  rw [← Category.assoc, hh, zero_comp]

/-- 可換な二つの冪等元を完全三角形の第三対象の冪等元へ延長できる。 -/
theorem complete_triangle_idempotent (T : Triangle C) (hT : T ∈ distTriang C)
    (p : T.obj₁ ⟶ T.obj₁) (q : T.obj₂ ⟶ T.obj₂)
    (hp : p ≫ p = p) (hq : q ≫ q = q) (hf : T.mor₁ ≫ q = p ≫ T.mor₁) :
    ∃ r : T.obj₃ ⟶ T.obj₃, r ≫ r = r ∧ T.mor₂ ≫ r = q ≫ T.mor₂ ∧
      T.mor₃ ≫ p⟦(1 : ℤ)⟧' = r ≫ T.mor₃ := by
  obtain ⟨c, hg, hh⟩ := complete_distinguished_triangle_morphism T T hT hT p q hf
  have hc₂ : T.mor₂ ≫ c ≫ c = q ≫ T.mor₂ := by
    rw [← Category.assoc, hg, Category.assoc, hg, ← Category.assoc, hq]
  have hc₃ : T.mor₂ ≫ c ≫ c ≫ c = q ≫ T.mor₂ := by
    rw [← Category.assoc T.mor₂ c (c ≫ c), hg, Category.assoc, hc₂,
      ← Category.assoc, hq]
  have hcp₂ : (c ≫ c) ≫ T.mor₃ = T.mor₃ ≫ p⟦(1 : ℤ)⟧' := by
    rw [Category.assoc, ← hh, ← Category.assoc, ← hh, Category.assoc,
      ← Functor.map_comp, hp]
  have hcp₃ : ((c ≫ c) ≫ c) ≫ T.mor₃ = T.mor₃ ≫ p⟦(1 : ℤ)⟧' := by
    rw [Category.assoc, ← hh, ← Category.assoc, hcp₂, Category.assoc,
      ← Functor.map_comp, hp]
  have he : (c ≫ c - c) ≫ (c ≫ c - c) = 0 :=
    triangle_end_square_zero T hT _
      (by rw [Preadditive.comp_sub, hc₂, hg, sub_self])
      (by rw [Preadditive.sub_comp, hcp₂, ← hh, sub_self])
  let e : End T.obj₃ := .of c
  let r : End T.obj₃ := 3 • (e * e) - 2 • (e * e * e)
  have he' : (e * e - e) * (e * e - e) = 0 := End.ext he
  have hr' : r * r = r := by
    simpa only [r, nsmul_eq_mul, Nat.cast_ofNat] using idempotent_cubic e he'
  have hr := congrArg End.asHom hr'
  have hrdef : r.asHom = 3 • (c ≫ c) - 2 • (c ≫ c ≫ c) := rfl
  refine ⟨r.asHom, hr, ?_, ?_⟩
  · rw [hrdef]
    simp only [Preadditive.comp_sub, Preadditive.comp_nsmul, hc₂, hc₃]
    abel
  · rw [hrdef]
    rw [← Category.assoc c c c]
    simp only [Preadditive.sub_comp, Preadditive.nsmul_comp, hcp₂, hcp₃]
    abel

end SerrePositivity

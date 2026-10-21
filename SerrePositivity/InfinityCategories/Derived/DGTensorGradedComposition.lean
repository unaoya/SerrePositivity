module
public import SerrePositivity.InfinityCategories.Derived.DGTensorClosedCycles
/-!
概要：任意次数の実 tensor の合成と Koszul 符号を照合する。
方針：豊穣合成の式を通常順合成へ戻し、同じ整数次数の符号を計算する。
規約：追加の Small 性・平坦性を仮定しない。使われ方：全次元 tensor 候補の HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 第一因子の units スカラーを同じ実 tensor の外へ移す。 -/
lemma dgTensorElement_units_smul_left {x y : DGTensorCategory R B C} {p q n : ℤ}
    (f : GradedHom R x.1 y.1 p) (g : GradedHom R x.2 y.2 q) (hn : p + q = n) (e : ℤˣ) :
    dgTensorElement R (e • f) g hn = e • dgTensorElement R f g hn := by
  simp [dgTensorElement, Units.smul_def, TensorProduct.smul_tmul]
/-- 第二因子の units スカラーを同じ実 tensor の外へ移す。 -/
lemma dgTensorElement_units_smul_right {x y : DGTensorCategory R B C} {p q n : ℤ}
    (f : GradedHom R x.1 y.1 p) (g : GradedHom R x.2 y.2 q) (hn : p + q = n) (e : ℤˣ) :
    dgTensorElement R f (e • g) hn = e • dgTensorElement R f g hn := by
  simp [dgTensorElement, Units.smul_def, TensorProduct.tmul_smul]
/-- 任意次数の実 tensor の通常順合成は、Koszul 符号を持つ同じ二合成の tensor。 -/
lemma dgTensorElement_compose {x y z : DGTensorCategory R B C} {p q r s n : ℤ}
    (f₁ : GradedHom R x.1 y.1 p) (f₂ : GradedHom R x.2 y.2 q)
    (g₁ : GradedHom R y.1 z.1 r) (g₂ : GradedHom R y.2 z.2 s)
    (hn : (p + q) + (r + s) = n) :
    compose R (dgTensorElement R g₁ g₂ rfl) (dgTensorElement R f₁ f₂ rfl) hn =
      (p * s).negOnePow • dgTensorElement R
        (compose R g₁ f₁ rfl) (compose R g₂ f₂ rfl) (by omega) := by
  unfold compose
  rw [dgTensor_forward, dgTensorElement_units_smul_left, dgTensorElement_units_smul_right]
  simp only [smul_smul, ← Int.negOnePow_add]
  have he : (p + q) * (r + s) + q * r = p * s + (p * r + q * s) + 2 * (q * r) := by ring
  rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
end SerrePositivity.InfinityCategories

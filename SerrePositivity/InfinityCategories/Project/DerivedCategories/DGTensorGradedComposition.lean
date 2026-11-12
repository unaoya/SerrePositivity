module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGTensorClosedCycles
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [DGCategory R C]
/-- 第一因子の units スカラーを同じ実 tensor の外へ移す。 -/
lemma dgTensorElement_units_smul_left {x y : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C} {p q n : ℤ}
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.1 y.1 p) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.2 y.2 q) (hn : p + q = n) (e : ℤˣ) :
    _root_.SerrePositivity.DifferentialGraded.dgTensorElement R (e • f) g hn = e • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R f g hn := by
  simp [_root_.SerrePositivity.DifferentialGraded.dgTensorElement, Units.smul_def, TensorProduct.smul_tmul]
/-- 第二因子の units スカラーを同じ実 tensor の外へ移す。 -/
lemma dgTensorElement_units_smul_right {x y : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C} {p q n : ℤ}
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.1 y.1 p) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.2 y.2 q) (hn : p + q = n) (e : ℤˣ) :
    _root_.SerrePositivity.DifferentialGraded.dgTensorElement R f (e • g) hn = e • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R f g hn := by
  simp [_root_.SerrePositivity.DifferentialGraded.dgTensorElement, Units.smul_def, TensorProduct.tmul_smul]
/-- 任意次数の実 tensor の通常順合成は、Koszul 符号を持つ同じ二合成の tensor。 -/
lemma dgTensorElement_compose {x y z : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C} {p q r s n : ℤ}
    (f₁ : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.1 y.1 p) (f₂ : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.2 y.2 q)
    (g₁ : _root_.SerrePositivity.DifferentialGraded.GradedHom R y.1 z.1 r) (g₂ : _root_.SerrePositivity.DifferentialGraded.GradedHom R y.2 z.2 s)
    (hn : (p + q) + (r + s) = n) :
    _root_.SerrePositivity.DifferentialGraded.compose R (dgTensorElement R g₁ g₂ rfl) (dgTensorElement R f₁ f₂ rfl) hn =
      (p * s).negOnePow • _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
        (compose R g₁ f₁ rfl) (compose R g₂ f₂ rfl) (by omega) := by
  unfold _root_.SerrePositivity.DifferentialGraded.compose
  rw [dgTensor_forward, dgTensorElement_units_smul_left, dgTensorElement_units_smul_right]
  simp only [smul_smul, ← Int.negOnePow_add]
  have he : (p + q) * (r + s) + q * r = p * s + (p * r + q * s) + 2 * (q * r) := by ring
  rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.DifferentialGraded.Category.TensorElements

/-! # tensor積dg圏の通常順合成の符号 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C]

lemma dgTensorElement_units_smul {x y : DGTensorCategory A B C} {p q n : ℤ}
    (f : GradedHom A x.1 y.1 p) (g : GradedHom A x.2 y.2 q) (hn : p + q = n)
    (a b : ℤˣ) :
    dgTensorElement A (a • f) (b • g) hn = (a * b) • dgTensorElement A f g hn := by
  simp only [dgTensorElement, Units.smul_def, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, map_zsmul, smul_smul, Units.val_mul, mul_comm]

/-- 通常順合成の交差符号は最初の第一因子と次の第二因子の次数積。 -/
lemma dgTensor_compose {x y z : DGTensorCategory A B C} {p q r s n : ℤ}
    (f₁ : GradedHom A x.1 y.1 p) (f₂ : GradedHom A x.2 y.2 q)
    (g₁ : GradedHom A y.1 z.1 r) (g₂ : GradedHom A y.2 z.2 s)
    (hn : (p + q) + (r + s) = n) :
    compose A (dgTensorElement A g₁ g₂ rfl) (dgTensorElement A f₁ f₂ rfl) hn =
      (p * s).negOnePow • dgTensorElement A
        (compose A g₁ f₁ rfl) (compose A g₂ f₂ rfl) (by omega) := by
  have hs : ((p + q) * (r + s)).negOnePow * (q * r).negOnePow =
      (p * s).negOnePow * ((p * r).negOnePow * (q * s).negOnePow) := by
    simp only [← Int.negOnePow_add]
    have he : (p + q) * (r + s) + q * r = p * s + (p * r + q * s) + 2 * (q * r) := by ring
    rw [he, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
  simp only [compose, dgTensor_forward, dgTensorElement_units_smul, smul_smul]
  rw [hs]

end SerrePositivity.DifferentialGraded

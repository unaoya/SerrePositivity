module
public import SerrePositivity.DifferentialGraded.Category.TensorElements

/-! # 中間の和次数を指定したtensor積の合成公式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C]

/-- 各因子と全体の中間次数を別々に指定して合成する。 -/
lemma dgTensor_forward_of_sum {x y z : DGTensorCategory A B C} {p q r s a b c d n : ℤ}
    (f₁ : GradedHom A x.1 y.1 p) (f₂ : GradedHom A x.2 y.2 q)
    (g₁ : GradedHom A y.1 z.1 r) (g₂ : GradedHom A y.2 z.2 s)
    (ha : p + q = a) (hb : r + s = b) (hc : p + r = c) (hd : q + s = d)
    (hn : a + b = n) :
    forward A (dgTensorElement A f₁ f₂ ha) (dgTensorElement A g₁ g₂ hb) hn =
      (q * r).negOnePow • dgTensorElement A
        (forward A f₁ g₁ hc) (forward A f₂ g₂ hd) (by omega) := by
  subst a b c d
  exact dgTensor_forward A f₁ f₂ g₁ g₂ hn

end SerrePositivity.DifferentialGraded

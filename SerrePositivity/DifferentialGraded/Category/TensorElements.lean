module
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Complexes.TensorInterchange

/-! # tensor積dg圏の純粋斉次Homと合成の交差符号 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : Type u) [CommRing A] {B : Type v} {C : Type w}
  [DGCategory A B] [DGCategory A C]

/-- 二つの斉次Homからtensor積dg圏の斉次Homを作る。 -/
def dgTensorElement {x y : DGTensorCategory A B C} {p q n : ℤ}
    (f : GradedHom A x.1 y.1 p) (g : GradedHom A x.2 y.2 q) (hn : p + q = n) :
    GradedHom A x y n :=
  ιTensorObj (x.1 ⟶[Complex A] y.1) (x.2 ⟶[Complex A] y.2) p q n hn (f ⊗ₜ[A] g)

/-- 豊穣順合成の交差符号は最初の第二因子と次の第一因子の次数積。 -/
lemma dgTensor_forward {x y z : DGTensorCategory A B C} {p q r s n : ℤ}
    (f₁ : GradedHom A x.1 y.1 p) (f₂ : GradedHom A x.2 y.2 q)
    (g₁ : GradedHom A y.1 z.1 r) (g₂ : GradedHom A y.2 z.2 s)
    (hn : (p + q) + (r + s) = n) :
    forward A (dgTensorElement A f₁ f₂ rfl) (dgTensorElement A g₁ g₂ rfl) hn =
      (q * r).negOnePow • dgTensorElement A
        (forward A f₁ g₁ rfl) (forward A f₂ g₂ rfl) (by omega) := by
  unfold forward dgTensorElement
  rw [dgTensor_composition]
  change (eComp (Complex A) x.1 y.1 z.1 ⊗ₘ eComp (Complex A) x.2 y.2 z.2).f n
    ((tensorμ (x.1 ⟶[Complex A] y.1) (x.2 ⟶[Complex A] y.2)
      (y.1 ⟶[Complex A] z.1) (y.2 ⟶[Complex A] z.2)).f n
      (SerrePositivity.cochainTensorQuadι _ _ _ _ p q r s n (by omega)
        ((f₁ ⊗ₜ[A] f₂) ⊗ₜ[A] (g₁ ⊗ₜ[A] g₂)))) = _
  rw [tensorμ_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [SerrePositivity.cochainTensorQuadι_apply]
  exact congrArg (fun t : (x ⟶[Complex A] z).X n => ((q * r).negOnePow : ℤ) • t)
    (tensorMap_apply (eComp (Complex A) x.1 y.1 z.1) (eComp (Complex A) x.2 y.2 z.2)
      (p + r) (q + s) n (by omega)
      (ιTensorObj (x.1 ⟶[Complex A] y.1) (y.1 ⟶[Complex A] z.1) p r (p + r) rfl (f₁ ⊗ₜ[A] g₁))
      (ιTensorObj (x.2 ⟶[Complex A] y.2) (y.2 ⟶[Complex A] z.2) q s (q + s) rfl (f₂ ⊗ₜ[A] g₂)))

end SerrePositivity.DifferentialGraded

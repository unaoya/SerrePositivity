module
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainComposition

/-! # 全次数tensor写像の閉零chain mapとの一致 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 左tensorの全Hom写像は通常のchain mapのwhiskerLeftと一致する。 -/
lemma tensorLeftHom_ofHom (K P Q : Complex A) (f : P ⟶ Q) :
    (tensorLeftHom K P Q).f 0 (Cochain.ofHom f) = Cochain.ofHom (K ◁ f) := by
  apply Cochain.ext₀
  intro a
  apply mapBifunctor.hom_ext
  intro i j ha
  change i + j = a at ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((tensorLeftHom K P Q).f 0 (Cochain.ofHom f)).v a a (add_zero a)
    (ιTensorObj K P i j a ha (x ⊗ₜ[A] y)) =
      (K ◁ f).f a (ιTensorObj K P i j a ha (x ⊗ₜ[A] y))
  rw [tensorLeftHom_apply_of_sum K P Q 0 i j a j a ha (add_zero j) (add_zero a),
    whiskerLeft_apply]
  simp only [zero_mul, Int.negOnePow_zero, one_smul, Cochain.ofHom_v]

end SerrePositivity.DifferentialGraded

module
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain

/-! # 閉零の左写像を持つcochain tensorの右前合成自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorZeroCochain_precomp_right {P P' Q R T : Complex A}
    (F : P ⟶ P') (c : Q ⟶ R) (g : Cochain R T 0) :
    (Cochain.ofHom (P ◁ c)).comp (tensorZeroCochain (Cochain.ofHom F) g) (zero_add 0) =
    tensorZeroCochain (Cochain.ofHom F) ((Cochain.ofHom c).comp g (zero_add 0)) := by
  apply Cochain.ext₀
  intro n
  apply mapBifunctor.hom_ext
  intro i j hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change ((Cochain.ofHom (P ◁ c)).comp (tensorZeroCochain (Cochain.ofHom F) g)
      (zero_add 0)).v n n (add_zero n) (ιTensorObj P Q i j n hn (x ⊗ₜ[A] y)) =
    (tensorZeroCochain (Cochain.ofHom F) ((Cochain.ofHom c).comp g (zero_add 0))).v n n
      (add_zero n) (ιTensorObj P Q i j n hn (x ⊗ₜ[A] y))
  rw [cochain_ofHom_comp_apply, whiskerLeft_apply, tensorZeroCochain_apply,
    tensorZeroCochain_apply, cochain_ofHom_comp_apply]

end SerrePositivity.DifferentialGraded

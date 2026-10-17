module
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorClosedZero

/-! # 前方二因子を保つcochain持ち上げとchain mapによる前合成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma prefixTensor_cochain_precomp (K E P Q T U V : Complex A) (p : ℤ)
    (m : P ⊗ Q ⟶ T) (f : Cochain T U p) (post : K ⊗ (E ⊗ U) ⟶ V) :
    (Cochain.ofHom (((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom) ≫
      K ◁ (E ◁ m))).comp
      (((tensorLeftHom K (E ⊗ T) (E ⊗ U)).f p ((tensorLeftHom E T U).f p f)).comp
        (Cochain.ofHom post) (add_zero p)) (zero_add p) =
    ((Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ U)).f p
        ((tensorLeftHom E (P ⊗ Q) U).f p
          ((Cochain.ofHom m).comp f (zero_add p)))) (zero_add p)).comp
      (Cochain.ofHom post) (add_zero p) := by
  rw [tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom]
  simp only [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

end SerrePositivity.DifferentialGraded

module
public import SerrePositivity.DifferentialGraded.Complexes.PrefixTensorCochainPostcompose

/-! # 結合的な先頭追加と後方cochainの持ち上げ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma prefixTensor_cochain_action_left (K E P P' Q R T V : Complex A) (p : ℤ)
    (f : Cochain P P' p) (pre : K ⊗ (E ⊗ P') ⟶ R) (cmp : R ⊗ Q ⟶ V)
    (m : P' ⊗ Q ⟶ T) (post : K ⊗ (E ⊗ T) ⟶ V)
    (ha : (pre ▷ Q) ≫ cmp = (α_ K (E ⊗ P') Q).hom ≫ K ◁ (α_ E P' Q).hom ≫
      K ◁ (E ◁ m) ≫ post) :
    ((tensorRightHom Q (K ⊗ (E ⊗ P)) R).f p
      (((tensorLeftHom K (E ⊗ P) (E ⊗ P')).f p ((tensorLeftHom E P P').f p f)).comp
        (Cochain.ofHom pre) (add_zero p))).comp (Cochain.ofHom cmp) (add_zero p) =
    ((Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ T)).f p
        ((tensorLeftHom E (P ⊗ Q) T).f p
          (((tensorRightHom Q P P').f p f).comp (Cochain.ofHom m) (add_zero p))))
      (zero_add p)).comp (Cochain.ofHom post) (add_zero p) := by
  rw [tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ha]
  exact prefixTensor_cochain_middle_postcompose K E P P' Q T V p f m post

lemma prefixTensor_cochain_action_right (K E P Q Q' T V : Complex A) (p : ℤ)
    (f : Cochain Q Q' p) (cmp : (K ⊗ (E ⊗ P)) ⊗ Q' ⟶ V)
    (m : P ⊗ Q' ⟶ T) (post : K ⊗ (E ⊗ T) ⟶ V)
    (ha : cmp = (α_ K (E ⊗ P) Q').hom ≫ K ◁ (α_ E P Q').hom ≫ K ◁ (E ◁ m) ≫ post) :
    ((tensorLeftHom (K ⊗ (E ⊗ P)) Q Q').f p f).comp (Cochain.ofHom cmp) (add_zero p) =
    ((Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ T)).f p
        ((tensorLeftHom E (P ⊗ Q) T).f p
          (((tensorLeftHom P Q Q').f p f).comp (Cochain.ofHom m) (add_zero p))))
      (zero_add p)).comp (Cochain.ofHom post) (add_zero p) := by
  rw [ha]
  exact prefixTensor_cochain_right_postcompose K E P Q Q' T V p f m post

end SerrePositivity.DifferentialGraded

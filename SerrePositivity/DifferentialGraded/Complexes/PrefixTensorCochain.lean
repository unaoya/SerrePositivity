module
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainFactors

/-! # 前方二因子を保った右tensorの括弧変更とcochainの整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 二つの固定前方因子の後のcochainは、右tensorの括弧変更と可換する。 -/
lemma prefixTensor_cochain_middle (K E P P' Q : Complex A) (p : ℤ) (f : Cochain P P' p) :
    ((tensorRightHom Q (K ⊗ (E ⊗ P)) (K ⊗ (E ⊗ P'))).f p
      ((tensorLeftHom K (E ⊗ P) (E ⊗ P')).f p ((tensorLeftHom E P P').f p f))).comp
      (Cochain.ofHom ((α_ K (E ⊗ P') Q).hom ≫ K ◁ (α_ E P' Q).hom)) (add_zero p) =
    (Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ (P' ⊗ Q))).f p
        ((tensorLeftHom E (P ⊗ Q) (P' ⊗ Q)).f p
          ((tensorRightHom Q P P').f p f))) (zero_add p) := by
  rw [Cochain.ofHom_comp, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_second_is_zero_cochain,
    associator_hom_cochain_middle,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp,
    associator_hom_cochain_middle, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]

/-- 最後の右因子のcochainも、二つの固定前方因子の括弧変更と可換する。 -/
lemma prefixTensor_cochain_right (K E P Q Q' : Complex A) (p : ℤ) (f : Cochain Q Q' p) :
    ((tensorLeftHom (K ⊗ (E ⊗ P)) Q Q').f p f).comp
      (Cochain.ofHom ((α_ K (E ⊗ P) Q').hom ≫ K ◁ (α_ E P Q').hom)) (add_zero p) =
    (Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ (P ⊗ Q'))).f p
        ((tensorLeftHom E (P ⊗ Q) (P ⊗ Q')).f p
          ((tensorLeftHom P Q Q').f p f))) (zero_add p) := by
  rw [Cochain.ofHom_comp, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_second_is_zero_cochain,
    associator_hom_cochain_right,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp,
    associator_hom_cochain_right, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]

end SerrePositivity.DifferentialGraded

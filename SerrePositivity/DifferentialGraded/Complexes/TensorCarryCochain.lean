module
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainFactors
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorClosedZero
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainInterchange

/-! # 結合的な先頭作用の下での任意次数cochainの連結への輸送 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorRight_cochain_chain_naturality (P P' Q Q' : Complex A) (p : ℤ)
    (f : Cochain P P' p) (g : Q ⟶ Q') :
    (Cochain.ofHom (P ◁ g)).comp ((tensorRightHom Q' P P').f p f) (zero_add p) =
    ((tensorRightHom Q P P').f p f).comp (Cochain.ofHom (P' ◁ g)) (add_zero p) := by
  have h := tensorCochain_interchange P P' Q Q' p 0 p (add_zero p) (zero_add p)
    f (Cochain.ofHom g)
  simp only [mul_zero, Int.negOnePow_zero, one_smul, tensorLeftHom_ofHom] at h
  exact h.symm

lemma tensorCarry_cochain (K P P' Q T T' R S : Complex A) (p : ℤ)
    (f : Cochain P P' p) (g : Cochain T T' p)
    (m : P ⊗ Q ⟶ T) (n : P' ⊗ Q ⟶ T') (r : K ⊗ P' ⟶ R)
    (s : K ⊗ T' ⟶ S) (t : R ⊗ Q ⟶ S)
    (hm : (Cochain.ofHom m).comp g (zero_add p) =
      ((tensorRightHom Q P P').f p f).comp (Cochain.ofHom n) (add_zero p))
    (ha : (r ▷ Q) ≫ t = (α_ K P' Q).hom ≫ K ◁ n ≫ s) :
    (Cochain.ofHom ((α_ K P Q).hom ≫ K ◁ m)).comp
      (((tensorLeftHom K T T').f p g).comp (Cochain.ofHom s) (add_zero p)) (zero_add p) =
    ((tensorRightHom Q (K ⊗ P) R).f p
      (((tensorLeftHom K P P').f p f).comp (Cochain.ofHom r) (add_zero p))).comp
      (Cochain.ofHom t) (add_zero p) := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain
      (Cochain.ofHom (K ◁ m)), ← tensorLeftHom_ofHom,
    ← tensorLeftHom_cochain_comp, hm, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← associator_hom_cochain_middle,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  rw [tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ha]

lemma tensorRight_action_cochain (E H P Q T R S : Complex A) (p : ℤ)
    (f : Cochain E H p) (m : P ⊗ Q ⟶ T) (n : H ⊗ P ⟶ R)
    (r : R ⊗ Q ⟶ S) (s : H ⊗ T ⟶ S)
    (ha : (n ▷ Q) ≫ r = (α_ H P Q).hom ≫ H ◁ m ≫ s) :
    (Cochain.ofHom ((α_ E P Q).hom ≫ E ◁ m)).comp
      (((tensorRightHom T E H).f p f).comp (Cochain.ofHom s) (add_zero p)) (zero_add p) =
    ((tensorRightHom Q (E ⊗ P) R).f p
      (((tensorRightHom P E H).f p f).comp (Cochain.ofHom n) (add_zero p))).comp
      (Cochain.ofHom r) (add_zero p) := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom (E ◁ m)),
    tensorRight_cochain_chain_naturality,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← associator_hom_cochain_left,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  rw [tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ha]

end SerrePositivity.DifferentialGraded

module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureHeadNaturality
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainFactors

/-! # ε消去と右tensor・括弧変更の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 左端εの消去は右tensorを追加してもassociatorを通じて一致する。 -/
lemma eraseHead_tensorRight (P Q : Complex A) :
    (tensorRightHom Q (epsilonComplex A ⊗ P) P).f 1 (eraseHead A P) =
    (Cochain.ofHom (α_ (epsilonComplex A) P Q).hom).comp
      (eraseHead A (P ⊗ Q)) (zero_add 1) := by
  have hunit : (α_ (𝟙_ (Complex A)) P Q).hom ≫ (λ_ (P ⊗ Q)).hom =
      (λ_ P).hom ▷ Q := by monoidal
  have h := associator_hom_cochain_left (epsilonComplex A) (𝟙_ (Complex A)) P Q 1
    (eraseEpsilon A)
  change ((tensorRightHom Q (epsilonComplex A ⊗ P) ((𝟙_ (Complex A)) ⊗ P)).f 1
    (eraseRightTensor A P)).comp (Cochain.ofHom (α_ (𝟙_ (Complex A)) P Q).hom)
      (add_zero 1) =
    (Cochain.ofHom (α_ (epsilonComplex A) P Q).hom).comp
      (eraseRightTensor A (P ⊗ Q)) (zero_add 1) at h
  rw [eraseHead, tensorRightHom_cochain_comp, tensorRightHom_ofHom]
  rw [← hunit, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_second_is_zero_cochain, h,
    Cochain.comp_assoc_of_first_is_zero_cochain]
  rfl

/-- 中間ε消去と二段階の括弧変更の整合式。 -/
lemma eraseMiddle_tensorRight (K P Q : Complex A) :
    (Cochain.ofHom ((α_ K (epsilonComplex A ⊗ P) Q).hom ≫
      K ◁ (α_ (epsilonComplex A) P Q).hom)).comp
        (eraseMiddle A K (P ⊗ Q)) (zero_add 1) =
    ((tensorRightHom Q (K ⊗ (epsilonComplex A ⊗ P)) (K ⊗ P)).f 1
      (eraseMiddle A K P)).comp (Cochain.ofHom (α_ K P Q).hom) (add_zero 1) := by
  rw [eraseMiddle_eq_tensorLeft, eraseMiddle_eq_tensorLeft]
  rw [associator_hom_cochain_middle, eraseHead_tensorRight,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]

end SerrePositivity.DifferentialGraded.DGQuotient

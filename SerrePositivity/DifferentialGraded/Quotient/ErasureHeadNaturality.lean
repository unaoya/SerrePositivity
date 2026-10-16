module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureHead

/-! # 左端・中間ε消去の右因子のchain mapに関する自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

lemma eraseHead_naturality (P Q : Complex A) (f : P ⟶ Q) :
    (Cochain.ofHom ((epsilonComplex A) ◁ f)).comp (eraseHead A Q) (zero_add 1) =
      (eraseHead A P).comp (Cochain.ofHom f) (add_zero 1) := by
  have h := tensorCochain_interchange (epsilonComplex A) (𝟙_ (Complex A)) P Q
    1 0 1 (add_zero 1) (zero_add 1) (eraseEpsilon A) (Cochain.ofHom f)
  simp only [mul_zero, Int.negOnePow_zero, one_smul, tensorLeftHom_ofHom] at h
  change (eraseRightTensor A P).comp (Cochain.ofHom ((𝟙_ (Complex A)) ◁ f)) (add_zero 1) =
    (Cochain.ofHom ((epsilonComplex A) ◁ f)).comp (eraseRightTensor A Q) (zero_add 1) at h
  rw [eraseHead, eraseHead, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← h,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    leftUnitor_naturality]

lemma eraseMiddle_naturality (K P Q : Complex A) (f : P ⟶ Q) :
    (Cochain.ofHom (K ◁ ((epsilonComplex A) ◁ f))).comp (eraseMiddle A K Q) (zero_add 1) =
      (eraseMiddle A K P).comp (Cochain.ofHom (K ◁ f)) (add_zero 1) := by
  rw [eraseMiddle_eq_tensorLeft, eraseMiddle_eq_tensorLeft,
    ← tensorLeftHom_ofHom K _ _ ((epsilonComplex A) ◁ f),
    ← tensorLeftHom_ofHom K _ _ f,
    ← tensorLeftHom_cochain_comp, ← tensorLeftHom_cochain_comp, eraseHead_naturality]

end SerrePositivity.DifferentialGraded.DGQuotient

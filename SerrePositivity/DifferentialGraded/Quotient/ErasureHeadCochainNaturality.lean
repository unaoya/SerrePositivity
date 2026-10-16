module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureHeadNaturality

/-! # 閉性を仮定しない次数0 cochainに対するε消去の自然性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

lemma eraseHead_cochain_zero (P Q : Complex A) (f : Cochain P Q 0) :
    ((tensorLeftHom (epsilonComplex A) P Q).f 0 f).comp (eraseHead A Q) (zero_add 1) =
      (eraseHead A P).comp f (add_zero 1) := by
  have h := tensorCochain_interchange (epsilonComplex A) (𝟙_ (Complex A)) P Q
    1 0 1 (add_zero 1) (zero_add 1) (eraseEpsilon A) f
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  change (eraseRightTensor A P).comp ((tensorLeftHom (𝟙_ (Complex A)) P Q).f 0 f)
      (add_zero 1) =
    ((tensorLeftHom (epsilonComplex A) P Q).f 0 f).comp (eraseRightTensor A Q) (zero_add 1) at h
  rw [eraseHead, eraseHead, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← h,
    Cochain.comp_assoc_of_third_is_zero_cochain, leftUnitor_hom_cochain,
    ← Cochain.comp_assoc_of_second_is_zero_cochain]

lemma eraseMiddle_cochain_zero (K P Q : Complex A) (f : Cochain P Q 0) :
    ((tensorLeftHom K (epsilonComplex A ⊗ P) (epsilonComplex A ⊗ Q)).f 0
      ((tensorLeftHom (epsilonComplex A) P Q).f 0 f)).comp (eraseMiddle A K Q) (zero_add 1) =
    (eraseMiddle A K P).comp ((tensorLeftHom K P Q).f 0 f) (add_zero 1) := by
  rw [eraseMiddle_eq_tensorLeft, eraseMiddle_eq_tensorLeft,
    ← tensorLeftHom_cochain_comp, ← tensorLeftHom_cochain_comp, eraseHead_cochain_zero]

end SerrePositivity.DifferentialGraded.DGQuotient

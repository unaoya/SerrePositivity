module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureInterchange
public import SerrePositivity.DifferentialGraded.Complexes.UnitorCochainNaturality

/-! # 単位因子を除いた中間ε消去と後方cochainの反交換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 中間εを消した後に後方cochainを作用させる順序を交換すると負号が付く。 -/
lemma eraseMiddle_tail_anticommute (K P Q : Complex A) (f : Cochain P Q 1) :
    (eraseMiddle A K P).comp ((tensorLeftHom K P Q).f 1 f)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom K (epsilonComplex A ⊗ P) (epsilonComplex A ⊗ Q)).f 1
      ((tensorLeftHom (epsilonComplex A) P Q).f 1 f)).comp
      (eraseMiddle A K Q) (show (1 : ℤ) + 1 = 2 by omega)) := by
  rw [eraseMiddle, eraseMiddle, Cochain.comp_assoc_of_second_is_zero_cochain,
    ← leftUnitor_hom_cochain_tensor,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    eraseRightTensor_prefixed_anticommute, Cochain.neg_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain]

/-- 標準ε生成元を含む純tensorの消去は、左因子の次数の符号を持つ。 -/
lemma eraseMiddle_generator (K Q : Complex A) (i j b a n : ℤ)
    (hb : (-1) + j = b) (ha : i + b = a) (hn : a + 1 = n)
    (x : K.X i) (y : Q.X j) :
    (eraseMiddle A K Q).v a n hn
      (ιTensorObj K (epsilonComplex A ⊗ Q) i b a ha
        (x ⊗ₜ[A] ιTensorObj (epsilonComplex A) Q (-1) j b hb
          ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] y))) =
    i.negOnePow • ιTensorObj K Q i j n (by omega) (x ⊗ₜ[A] y) := by
  rw [eraseMiddle, cochain_comp_ofHom_apply,
    tensorLeftHom_apply_of_sum K (epsilonComplex A ⊗ Q) (𝟙_ (Complex A) ⊗ Q)
      1 i b a j n ha (by omega) hn,
    eraseRightTensor_apply, eraseEpsilon_generator, chain_units_smul,
    whiskerLeft_apply, leftUnitor_hom_generator]
  simp only [one_mul]

end SerrePositivity.DifferentialGraded.DGQuotient

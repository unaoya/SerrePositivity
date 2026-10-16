module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureTensorRight

/-! # 右tensor後の括弧変更・後方chain mapと先頭ε消去 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- 後方tensorのchain mapを適用してからのε消去を、先のε消去へ移す。 -/
lemma eraseMiddle_tensorRight_naturality (K P Q T : Complex A) (f : P ⊗ Q ⟶ T) :
    (Cochain.ofHom ((α_ K (epsilonComplex A ⊗ P) Q).hom ≫
      K ◁ (α_ (epsilonComplex A) P Q).hom ≫ K ◁ ((epsilonComplex A) ◁ f))).comp
        (eraseMiddle A K T) (zero_add 1) =
    ((tensorRightHom Q (K ⊗ (epsilonComplex A ⊗ P)) (K ⊗ P)).f 1
      (eraseMiddle A K P)).comp
        (Cochain.ofHom ((α_ K P Q).hom ≫ K ◁ f)) (add_zero 1) := by
  rw [← Category.assoc, Cochain.ofHom_comp,
    Cochain.comp_assoc_of_first_is_zero_cochain, eraseMiddle_naturality,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    eraseMiddle_tensorRight, Cochain.comp_assoc_of_second_is_zero_cochain,
    ← Cochain.ofHom_comp]


end SerrePositivity.DifferentialGraded.DGQuotient

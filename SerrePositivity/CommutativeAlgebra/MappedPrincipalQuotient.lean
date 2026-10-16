module
public import SerrePositivity.CommutativeAlgebra.PrincipalAdicReductionAlgebra

/-! # The original extended principal ideal quotient and the original image-generator quotient -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
attribute [local instance] adicQuotientAlgebra principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (d : R) (S : Type u) [CommRing S] [Algebra R S]

/-- Compare the two actual quotient rings while retaining their original quotient-base actions. -/
def mappedPrincipalQuotientAlgEquiv :
    (S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})) ≃ₐ[R ⧸ Ideal.span {d}]
      S ⧸ Ideal.span {algebraMap R S d} := by
  have hi : Ideal.map (algebraMap R S) (Ideal.span {d}) = Ideal.span {algebraMap R S d} := by
    rw [Ideal.map_span, Set.image_singleton]
  let e := Ideal.quotientEquivAlgOfEq R hi
  exact
    { e.toRingEquiv with
      commutes' x := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        change e (Ideal.Quotient.mk _ (algebraMap R S r)) =
          Ideal.Quotient.mk _ (algebraMap R S r)
        exact Ideal.quotientEquivAlgOfEq_mk R hi _ }

/-- The standard comparison retains every original representative. -/
lemma mappedPrincipalQuotientAlgEquiv_mk (s : S) :
    mappedPrincipalQuotientAlgEquiv R d S
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R S d}) s := rfl

/-- Its inverse also retains the same original representative. -/
lemma mappedPrincipalQuotientAlgEquiv_symm_mk (s : S) :
    (mappedPrincipalQuotientAlgEquiv R d S).symm
        (Ideal.Quotient.mk (Ideal.span {algebraMap R S d}) s) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R S) (Ideal.span {d})) s := by
  apply (mappedPrincipalQuotientAlgEquiv R d S).injective
  rw [AlgEquiv.apply_symm_apply, mappedPrincipalQuotientAlgEquiv_mk]

end SerrePositivity

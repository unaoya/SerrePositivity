module
public import SerrePositivity.CommutativeAlgebra.PrincipalAdicReductionAlgebra

/-! # The original principal quotient map of an algebra equivalence is an equivalence -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
attribute [local instance] principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (d : R)
    {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Use the original forward and inverse quotient algebra maps
without changing the quotient actions. -/
def principalAdicReductionAlgEquiv (e : S ≃ₐ[R] T) :
    (S ⧸ Ideal.span {algebraMap R S d}) ≃ₐ[R ⧸ Ideal.span {d}]
      T ⧸ Ideal.span {algebraMap R T d} := by
  let f := principalAdicReductionAlgHom R d e.toAlgHom
  let g := principalAdicReductionAlgHom R d e.symm.toAlgHom
  have hfg : f.comp g = AlgHom.id (R ⧸ Ideal.span {d}) _ := by
    ext x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (e (e.symm t)) = Ideal.Quotient.mk _ t
    rw [e.apply_symm_apply]
  have hgf : g.comp f = AlgHom.id (R ⧸ Ideal.span {d}) _ := by
    ext x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (e.symm (e s)) = Ideal.Quotient.mk _ s
    rw [e.symm_apply_apply]
  exact AlgEquiv.ofAlgHom f g hfg hgf

/-- The forward map is exactly the already constructed original quotient algebra map. -/
lemma principalAdicReductionAlgEquiv_toAlgHom (e : S ≃ₐ[R] T) :
    (principalAdicReductionAlgEquiv R d e).toAlgHom =
      principalAdicReductionAlgHom R d e.toAlgHom := rfl

/-- On representatives this is the original algebra equivalence followed
by the original quotient. -/
lemma principalAdicReductionAlgEquiv_mk (e : S ≃ₐ[R] T) (s : S) :
    principalAdicReductionAlgEquiv R d e (Ideal.Quotient.mk (Ideal.span {algebraMap R S d}) s) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R T d}) (e s) := rfl

end SerrePositivity

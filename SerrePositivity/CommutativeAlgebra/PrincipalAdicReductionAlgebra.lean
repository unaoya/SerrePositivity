module
public import SerrePositivity.CommutativeAlgebra.PrincipalAdicFaithfulDescent

/-! # The original principal residue map as an algebra homomorphism -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
attribute [local instance] principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (d : R)
    {S T : Type u} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The standard quotient ring map, over the original quotient of the coefficient ring. -/
def principalAdicReductionAlgHom (f : S →ₐ[R] T) :
    (S ⧸ Ideal.span {algebraMap R S d}) →ₐ[R ⧸ Ideal.span {d}]
      T ⧸ Ideal.span {algebraMap R T d} := by
  let g : (S ⧸ Ideal.span {algebraMap R S d}) →+*
      T ⧸ Ideal.span {algebraMap R T d} :=
    Ideal.quotientMap (Ideal.span {algebraMap R T d}) f.toRingHom (by
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      change f (algebraMap R S d) ∈ Ideal.span {algebraMap R T d}
      rw [AlgHom.commutes]
      exact Ideal.mem_span_singleton_self _)
  exact
    { g with
      commutes' x := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        change Ideal.Quotient.mk (Ideal.span {algebraMap R T d}) (f (algebraMap R S r)) =
          Ideal.Quotient.mk (Ideal.span {algebraMap R T d}) (algebraMap R T r)
        rw [AlgHom.commutes] }

/-- Its underlying linear map is exactly the previously used original residue map. -/
lemma principalAdicReductionAlgHom_toLinearMap (f : S →ₐ[R] T) :
    (principalAdicReductionAlgHom R d f).toLinearMap = principalAdicReductionMap d f := by
  apply LinearMap.ext
  intro x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- On an original representative the map is the original algebra map followed by the quotient. -/
lemma principalAdicReductionAlgHom_mk (f : S →ₐ[R] T) (s : S) :
    principalAdicReductionAlgHom R d f (Ideal.Quotient.mk (Ideal.span {algebraMap R S d}) s) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R T d}) (f s) := rfl

end SerrePositivity

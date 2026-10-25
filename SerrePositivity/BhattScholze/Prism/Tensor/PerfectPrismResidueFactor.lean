module
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrismHom
public import SerrePositivity.CommutativeAlgebra.MappedPrincipalQuotient

/-! # Original residue factors of a morphism of perfect prisms -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
attribute [local instance] adicQuotientAlgebra
variable {p : ℕ} [Fact p.Prime] {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]

/-- The extended base ideal gives the target prism's own residue ring, with
the coefficient action induced by the original prism morphism. -/
def perfectPrismResidueFactorAlgEquiv
    (PR : OrientedPrism p R) (PS : OrientedPrism p S)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (f : OrientedPrism.Hom PR PS) (hf : f.toRingHom = algebraMap R S) :
    letI : Algebra (R ⧸ PR.ideal) (S ⧸ PS.ideal) := f.quotientMap.toAlgebra
    (S ⧸ Ideal.map (algebraMap R S) PR.ideal) ≃ₐ[R ⧸ PR.ideal] S ⧸ PS.ideal := by
  letI : Algebra (R ⧸ PR.ideal) (S ⧸ PS.ideal) := f.quotientMap.toAlgebra
  have hi : Ideal.map (algebraMap R S) PR.ideal = PS.ideal := by
    rw [← hf]
    exact f.map_ideal_eq_of_perfect hR hS
  let e := Ideal.quotientEquivAlgOfEq R hi
  exact
    { e.toRingEquiv with
      commutes' x := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        change e (Ideal.Quotient.mk _ (algebraMap R S r)) =
          f.quotientMap (Ideal.Quotient.mk PR.ideal r)
        rw [Ideal.quotientEquivAlgOfEq_mk, OrientedPrism.Hom.quotientMap_mk, hf] }

/-- The factor comparison sends each original representative to itself. -/
lemma perfectPrismResidueFactorAlgEquiv_mk
    (PR : OrientedPrism p R) (PS : OrientedPrism p S)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (f : OrientedPrism.Hom PR PS) (hf : f.toRingHom = algebraMap R S) (s : S) :
    perfectPrismResidueFactorAlgEquiv PR PS hR hS f hf
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) PR.ideal) s) =
      Ideal.Quotient.mk PS.ideal s := rfl

/-- The inverse comparison retains the same representative as well. -/
lemma perfectPrismResidueFactorAlgEquiv_symm_mk
    (PR : OrientedPrism p R) (PS : OrientedPrism p S)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (f : OrientedPrism.Hom PR PS) (hf : f.toRingHom = algebraMap R S) (s : S) :
    letI : Algebra (R ⧸ PR.ideal) (S ⧸ PS.ideal) := f.quotientMap.toAlgebra
    (perfectPrismResidueFactorAlgEquiv PR PS hR hS f hf).symm
        (Ideal.Quotient.mk PS.ideal s) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R S) PR.ideal) s := by
  letI : Algebra (R ⧸ PR.ideal) (S ⧸ PS.ideal) := f.quotientMap.toAlgebra
  apply (perfectPrismResidueFactorAlgEquiv PR PS hR hS f hf).injective
  rw [AlgEquiv.apply_symm_apply, perfectPrismResidueFactorAlgEquiv_mk]

/-- The coefficient map after comparison is precisely the original prism quotient map. -/
lemma perfectPrismResidueFactorAlgEquiv_algebraMap
    (PR : OrientedPrism p R) (PS : OrientedPrism p S)
    (hR : PR.deltaStructure.IsPerfect) (hS : PS.deltaStructure.IsPerfect)
    (f : OrientedPrism.Hom PR PS) (hf : f.toRingHom = algebraMap R S)
    (x : R ⧸ PR.ideal) :
    perfectPrismResidueFactorAlgEquiv PR PS hR hS f hf
        (algebraMap (R ⧸ PR.ideal) (S ⧸ Ideal.map (algebraMap R S) PR.ideal) x) =
      f.quotientMap x := by
  letI : Algebra (R ⧸ PR.ideal) (S ⧸ PS.ideal) := f.quotientMap.toAlgebra
  exact (perfectPrismResidueFactorAlgEquiv PR PS hR hS f hf).commutes x

end SerrePositivity.BhattScholze

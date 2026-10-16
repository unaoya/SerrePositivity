module
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.HomologicalAlgebra.RegularPrincipalTor
public import SerrePositivity.CommutativeAlgebra.PrincipalAdicFaithfulDescent
public import SerrePositivity.HomologicalAlgebra.DerivedH0Algebra

/-! # Actual regular quotient of a pure derived algebra and its original Cartier quotient -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (d : R) (hd : IsSMulRegular R d)
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R)))
    [A.X.obj.IsGE 0] [A.X.obj.IsLE 0]
set_option quotPrecheck false in
local notation "H" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})

/-- Normalize by the identity on the original H⁰, then take its ordinary Cartier quotient. -/
def pureDerivedAlgebraCartierQuotientIso (hreg : IsSMulRegular H d) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    (boundedAboveDerivedBaseChange (q)).obj A.X ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q (H ⧸ Ideal.span {algebraMap R H d})) := by
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  let e : A.X ≅ boundedAboveDerivedSingleFunctor.obj H :=
    ObjectProperty.isoMk _ (normalizedPureHomologyIso A.X.obj 0)
  exact (boundedAboveDerivedBaseChange (q)).mapIso e ≪≫
    derivedQuotientModuleIsoOfRegular d hd H hreg ≪≫
    boundedAboveDerivedSingleFunctor.mapIso (principalAdicReductionEquiv d H).toModuleIso

/-- The actual quotient homology is the ordinary quotient of the unchanged original H⁰ ring. -/
def pureDerivedAlgebraCartierQuotientH0Iso (hreg : IsSMulRegular H d) :
    letI := derivedH0CommRing A
    letI := derivedH0Algebra A
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        ((boundedAboveDerivedBaseChange (q)).obj A.X).obj ≅
      ModuleCat.of Q (H ⧸ Ideal.span {algebraMap R H d}) := by
  letI := derivedH0CommRing A
  letI := derivedH0Algebra A
  exact (DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (pureDerivedAlgebraCartierQuotientIso R d hd A hreg)) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q) 0).app _

include hd in
/-- Regular base change preserves purity of the given original pure algebra object. -/
lemma pureDerivedAlgebraCartierQuotient_pure (hreg : IsSMulRegular H d) :
    ((boundedAboveDerivedBaseChange (q)).obj A.X).obj.IsGE 0 ∧
      ((boundedAboveDerivedBaseChange (q)).obj A.X).obj.IsLE 0 := by
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let e := DerivedCategory.Minus.ι.mapIso (pureDerivedAlgebraCartierQuotientIso R d hd A hreg)
  have hz (i : ℤ) (hi : i ≠ 0) : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj
        ((boundedAboveDerivedBaseChange (q)).obj A.X).obj) :=
    (derivedSingleHomology_isZero _ i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso e)
  exact ⟨(DerivedCategory.isGE_iff _ _).mpr (fun i hi => hz i (by omega)),
    (DerivedCategory.isLE_iff _ _).mpr (fun i hi => hz i (by omega))⟩

end SerrePositivity

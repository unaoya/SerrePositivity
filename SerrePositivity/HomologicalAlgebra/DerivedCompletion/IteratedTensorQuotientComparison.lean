module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotientBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RegularTensorReduction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionAlgebraObjects

/-! # The actual iterated completed tensor after regular principal base change

Both ordinary residue factors retain their independent Tor inputs. The outer
completion unit and the original inner completion unit determine the comparison.
-/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable (R : Type u) [CommRing R] (a b : R) (hb : IsSMulRegular R b)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {b})
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {b}
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {b})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {b})
set_option quotPrecheck false in
local notation "X" => (boundedAboveDerivedTensorAlgebra (R := R) S T).X
local notation "AP" => boundedAboveCompletedTensorAlgebra R a S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R b).obj AP

include hb in
/-- The quotient of the outer completion unit is the original actual isomorphism. -/
lemma iteratedTensor_outerQuotientUnit_isIso :
    IsIso (((boundedAboveDerivedBaseChange (q)).map
      ((boundedAboveDerivedCompletionUnit R b).app (AP).X)).hom) := by
  have aux (c : R) (hc : b ^ 1 = c) :
      IsIso ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {c}))).map
        ((boundedAboveDerivedCompletionUnit R b).app (AP).X)) := by
    subst c
    exact boundedAboveDerivedCompletion_quotient_unit_isIso R b hb 1 (AP).X
  have hi := aux b (pow_one b)
  change IsIso (DerivedCategory.Minus.ι.map
    ((boundedAboveDerivedBaseChange (q)).map
      ((boundedAboveDerivedCompletionUnit R b).app (AP).X)))
  infer_instance

/-- Quotient the original a,b-completed tensor, or a-complete the actual quotient tensor. -/
def iteratedCompletedTensorQuotientIso
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) :
    ((boundedAboveDerivedBaseChange (q)).obj (AD).X).obj ≅
      (derivedComplexCompletionFunctor Q ((q) a)).obj
        (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ).X.obj := by
  have := iteratedTensor_outerQuotientUnit_isIso R a b hb S T
  exact (asIso (((boundedAboveDerivedBaseChange (q)).map
      ((boundedAboveDerivedCompletionUnit R b).app (AP).X)).hom)).symm ≪≫
    (completionQuotientBaseChangeIso R a b hb X).symm ≪≫
    (derivedComplexCompletionFunctor Q ((q) a)).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (derivedTensorQuotientAlgebraIso (Ideal.span {b}) S T hS hT))

/-- The outer standard unit is removed by the comparison without replacing that unit. -/
lemma iteratedCompletedTensorQuotientIso_outer_unit
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) :
    (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R b).app (AP).X)).hom) ≫
        (iteratedCompletedTensorQuotientIso R a b hb S T hS hT).hom =
      (completionQuotientBaseChangeIso R a b hb X).inv ≫
        (derivedComplexCompletionFunctor Q ((q) a)).map
          (derivedTensorQuotientAlgebraIso (Ideal.span {b}) S T hS hT).hom.hom := by
  have := iteratedTensor_outerQuotientUnit_isIso R a b hb S T
  simp only [iteratedCompletedTensorQuotientIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_inv, IsIso.hom_inv_id_assoc]
  rfl

/-- Both original completion units are sent to the standard completion unit of the quotient tensor. -/
lemma iteratedCompletedTensorQuotientIso_units
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) :
    (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app X ≫
          (boundedAboveDerivedCompletionUnit R b).app (AP).X)).hom) ≫
        (iteratedCompletedTensorQuotientIso R a b hb S T hS hT).hom =
      (derivedComplexCompletionUnit Q ((q) a)).app
          ((boundedAboveDerivedBaseChange (q)).obj X).obj ≫
        (derivedComplexCompletionFunctor Q ((q) a)).map
          (derivedTensorQuotientAlgebraIso (Ideal.span {b}) S T hS hT).hom.hom := by
  rw [Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
    iteratedCompletedTensorQuotientIso_outer_unit, ← Category.assoc]
  have hu := completionQuotientBaseChangeComparison_unit R a b hb X
  have hi : (((boundedAboveDerivedBaseChange (q)).map
        ((boundedAboveDerivedCompletionUnit R a).app X)).hom) ≫
        (completionQuotientBaseChangeIso R a b hb X).inv =
      (derivedComplexCompletionUnit Q ((q) a)).app
        ((boundedAboveDerivedBaseChange (q)).obj X).obj := by
    rw [← hu]
    change ((derivedComplexCompletionUnit Q ((q) a)).app _ ≫
      (completionQuotientBaseChangeIso R a b hb X).hom) ≫
        (completionQuotientBaseChangeIso R a b hb X).inv = _
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hi]

/-- Separate regularity of the two factors supplies the two ordinary-residue Tor inputs. -/
def regularIteratedCompletedTensorQuotientIso
    (hs : IsSMulRegular S b) (ht : IsSMulRegular T b) :
    ((boundedAboveDerivedBaseChange (q)).obj (AD).X).obj ≅
      (derivedComplexCompletionFunctor Q ((q) a)).obj
        (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ).X.obj :=
  iteratedCompletedTensorQuotientIso R a b hb S T
    (scalarExtensionTorVanishing_principal_of_regular b hb (ModuleCat.of R S) hs)
    (scalarExtensionTorVanishing_principal_of_regular b hb (ModuleCat.of R T) ht)

end SerrePositivity.DerivedCompletion

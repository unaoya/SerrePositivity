module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedTensorQuotientComparison
public import SerrePositivity.HomologicalAlgebra.PureDerivedCartierRepresentatives
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IteratedTensorCartierAlgebra

/-! # The original linear Cartier comparison on completion units and representative classes -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
  principalAdicQuotientAlgebra
variable (R : Type u) [CommRing R] (a d : R) (hd : IsSMulRegular R d)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
set_option quotPrecheck false in
local notation "Q" => R ⧸ Ideal.span {d}
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk (Ideal.span {d})
set_option quotPrecheck false in
local notation "SQ" => S ⧸ Ideal.map (algebraMap R S) (Ideal.span {d})
set_option quotPrecheck false in
local notation "TQ" => T ⧸ Ideal.map (algebraMap R T) (Ideal.span {d})
local notation "X" => boundedAboveDerivedTensorAlgebra (R := R) S T
local notation "AP" => boundedAboveCompletedTensorAlgebra R a S T
set_option quotPrecheck false in
local notation "AD" => (boundedAboveCompletionCommMonFunctor R d).obj AP
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AD).X.obj
set_option quotPrecheck false in
local notation "CQ" => C ⧸ Ideal.span {algebraMap R C d}
local notation "RX" => boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ
set_option quotPrecheck false in
local notation "RC" => (boundedAboveCompletionCommMonFunctor Q ((q) a)).obj RX

/-- The original inverse tensor quotient comparison followed by the unchanged Cartier H⁰ map. -/
def iteratedCompletedTensorCartierH0Iso
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0) :
    letI : (AD).X.obj.IsGE 0 := hpure.1
    letI : (AD).X.obj.IsLE 0 := hpure.2
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (RC).X.obj ≅ ModuleCat.of Q CQ := by
  letI : (AD).X.obj.IsGE 0 := hpure.1
  letI : (AD).X.obj.IsLE 0 := hpure.2
  letI := derivedH0CommRing AD
  letI := derivedH0Algebra AD
  exact (DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (iteratedCompletedTensorQuotientIso R a d hd S T hS hT).symm ≪≫
    pureDerivedAlgebraCartierQuotientH0Iso R d hd AD hC

/-- On the original unit, the linear comparison is the Cartier image of both original units. -/
lemma iteratedCompletedTensorCartierH0Iso_units
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (z : (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange (q)).obj (X).X).obj) :
    letI : (AD).X.obj.IsGE 0 := hpure.1
    letI : (AD).X.obj.IsLE 0 := hpure.2
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj)
          ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
            (derivedTensorQuotientAlgebraIso (Ideal.span {d}) S T hS hT).hom.hom z)) =
      (pureDerivedAlgebraCartierQuotientH0Iso R d hd AD hC).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (((boundedAboveDerivedBaseChange (q)).map
            ((boundedAboveDerivedCompletionUnit R a).app (X).X ≫
              (boundedAboveDerivedCompletionUnit R d).app (AP).X)).hom) z) := by
  let : (AD).X.obj.IsGE 0 := hpure.1
  let : (AD).X.obj.IsLE 0 := hpure.2
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let H0 := DerivedCategory.homologyFunctor (ModuleCat Q) 0
  have hu := congrArg H0.map (iteratedCompletedTensorQuotientIso_inv_units
    R a d hd S T hS hT)
  rw [Functor.map_comp, Functor.map_comp] at hu
  have hz := congrArg (fun f => f z) hu
  simp only [ModuleCat.comp_apply] at hz
  change H0.map (iteratedCompletedTensorQuotientIso R a d hd S T hS hT).inv
      (H0.map ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj)
        (H0.map (derivedTensorQuotientAlgebraIso (Ideal.span {d}) S T hS hT).hom.hom z)) =
    H0.map (((boundedAboveDerivedBaseChange (q)).map
      ((boundedAboveDerivedCompletionUnit R a).app (X).X ≫
        (boundedAboveDerivedCompletionUnit R d).app (AP).X)).hom) z at hz
  exact congrArg (pureDerivedAlgebraCartierQuotientH0Iso R d hd AD hC).hom hz

/-- Original discrete source representatives keep their Cartier class under the comparison. -/
lemma iteratedCompletedTensorCartierH0Iso_single_map
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (U : Type u) [CommRing U] [Algebra R U] (hU : IsSMulRegular U d)
    (f : boundedAboveDerivedAlgebra (R := R) U ⟶ X) (s : U) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    letI := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) U)
    letI := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) U)
    let eU : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveDerivedAlgebra (R := R) U).X.obj ≃ₐ[R] U :=
      derivedSingleH0AlgEquiv (R := R) U
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj)
          ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
            (derivedTensorQuotientAlgebraIso (Ideal.span {d}) S T hS hT).hom.hom
            ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
              (((boundedAboveDerivedBaseChange (q)).map f.hom.hom).hom)
              ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R U)
                ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] s))))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
        (derivedH0AlgMap (f ≫ boundedAboveCompletionAlgebraUnit R a X ≫
            boundedAboveCompletionAlgebraUnit R d AP)
          (eU.symm s)) := by
  let : (AD).X.obj.IsGE 0 := hpure.1
  let : (AD).X.obj.IsLE 0 := hpure.2
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  let := derivedH0CommRing (boundedAboveDerivedAlgebra (R := R) U)
  let := derivedH0Algebra (boundedAboveDerivedAlgebra (R := R) U)
  rw [iteratedCompletedTensorCartierH0Iso_units]
  have h := pureDerivedAlgebraCartierQuotientH0Iso_single_map R d U hd hU AD hC
    (f ≫ boundedAboveCompletionAlgebraUnit R a X ≫
      boundedAboveCompletionAlgebraUnit R d AP) s
  have hu : (f ≫ boundedAboveCompletionAlgebraUnit R a X ≫
        boundedAboveCompletionAlgebraUnit R d AP).hom.hom =
      f.hom.hom ≫ ((boundedAboveDerivedCompletionUnit R a).app (X).X ≫
        (boundedAboveDerivedCompletionUnit R d).app (AP).X) := by
    change f.hom.hom ≫ ((boundedAboveCompletionAlgebraUnit R a X).hom.hom ≫
      (boundedAboveCompletionAlgebraUnit R d AP).hom.hom) = _
    rw [boundedAboveCompletionAlgebraUnit_hom, boundedAboveCompletionAlgebraUnit_hom]
  rw [hu, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
    Functor.map_comp] at h
  simp only [ModuleCat.comp_apply] at h
  exact h

/-- The linear comparison retains the original left factor's actual Cartier image. -/
lemma iteratedCompletedTensorCartierH0Iso_left
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hsrc : IsSMulRegular S d) (s : S) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj)
          ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
            (derivedTensorQuotientAlgebraIso (Ideal.span {d}) S T hS hT).hom.hom
            ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
              (((boundedAboveDerivedBaseChange (q)).map
                (boundedAboveDerivedTensorAlgebraLeft (R := R) S T).hom.hom).hom)
              ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R S)
                ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] s))))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
        (iteratedTensorH0LeftAlgHom R a d S T s) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  have h := iteratedCompletedTensorCartierH0Iso_single_map R a d hd S T hS hT hC hpure
    S hsrc (boundedAboveDerivedTensorAlgebraLeft (R := R) S T) s
  simp only [iteratedTensorH0LeftAlgHom, boundedAboveCompletedTensorAlgebraLeft,
    Category.assoc, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] at h ⊢
  exact h

/-- The linear comparison retains the original right factor's actual Cartier image. -/
lemma iteratedCompletedTensorCartierH0Iso_right
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0)
    (hsrc : IsSMulRegular T d) (s : T) :
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    (iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure).hom
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          ((derivedComplexCompletionUnit Q ((q) a)).app (RX).X.obj)
          ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
            (derivedTensorQuotientAlgebraIso (Ideal.span {d}) S T hS hT).hom.hom
            ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
              (((boundedAboveDerivedBaseChange (q)).map
                (boundedAboveDerivedTensorAlgebraRight (R := R) S T).hom.hom).hom)
              ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).inv.app (ModuleCat.of R T)
                ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk (Ideal.span {d})] s))))) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R C d})
        (iteratedTensorH0RightAlgHom R a d S T s) := by
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  have h := iteratedCompletedTensorCartierH0Iso_single_map R a d hd S T hS hT hC hpure
    T hsrc (boundedAboveDerivedTensorAlgebraRight (R := R) S T) s
  simp only [iteratedTensorH0RightAlgHom, boundedAboveCompletedTensorAlgebraRight,
    Category.assoc, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] at h ⊢
  exact h

/-- This is exactly the homology of the original derived Cartier comparison. -/
lemma iteratedCompletedTensorCartierH0Iso_eq_derived
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (hC : IsSMulRegular C d)
    (hpure : (AD).X.obj.IsGE 0 ∧ (AD).X.obj.IsLE 0) :
    letI : (AD).X.obj.IsGE 0 := hpure.1
    letI : (AD).X.obj.IsLE 0 := hpure.2
    letI := derivedH0CommRing AD
    letI := derivedH0Algebra AD
    iteratedCompletedTensorCartierH0Iso R a d hd S T hS hT hC hpure =
      (DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
        ((iteratedCompletedTensorQuotientIso R a d hd S T hS hT).symm ≪≫
          DerivedCategory.Minus.ι.mapIso (pureDerivedAlgebraCartierQuotientIso R d hd AD hC)) ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q) 0).app _ := by
  let : (AD).X.obj.IsGE 0 := hpure.1
  let : (AD).X.obj.IsLE 0 := hpure.2
  let := derivedH0CommRing AD
  let := derivedH0Algebra AD
  apply Iso.ext
  simp only [iteratedCompletedTensorCartierH0Iso, pureDerivedAlgebraCartierQuotientH0Iso,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

end SerrePositivity.DerivedCompletion

module
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeAugmentationComparison
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedTensorModuleNaturality
public import SerrePositivity.HomologicalAlgebra.RealizedSingleH0Normalization

/-! # The original tensor quotient comparison and ordinary residue tensor representatives -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
attribute [local instance] HasDerivedCategory.standard adicQuotientAlgebra
variable {R : Type u} [CommRing R] (I : Ideal R)
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
set_option quotPrecheck false in
local notation "q" => Ideal.Quotient.mk I
set_option quotPrecheck false in
local notation "Q" => R ⧸ I
set_option quotPrecheck false in
local notation "SQ" => S ⧸ I.map (algebraMap R S)
set_option quotPrecheck false in
local notation "TQ" => T ⧸ I.map (algebraMap R T)

/-- Ordinary tensor scalar extension followed by the two original residue-factor comparisons. -/
def quotientTensorScalarExtensionMap :
    (ModuleCat.extendScalars (q)).obj (ModuleCat.of R (S ⊗[R] T)) ⟶
      ModuleCat.of Q (SQ ⊗[Q] TQ) :=
  Functor.OplaxMonoidal.δ (ModuleCat.extendScalars (q)) (ModuleCat.of R S) (ModuleCat.of R T) ≫
    ((quotientAlgebraScalarExtensionEquiv I S).toModuleIso.hom ⊗ₘ
      (quotientAlgebraScalarExtensionEquiv I T).toModuleIso.hom)

/-- The original class of a pure tensor becomes precisely the two original residue classes. -/
lemma quotientTensorScalarExtensionMap_one_tmul (s : S) (t : T) :
    quotientTensorScalarExtensionMap I S T
        ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk I] (s ⊗ₜ[R] t)) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) s ⊗ₜ[Q]
        Ideal.Quotient.mk (I.map (algebraMap R T)) t := by
  rw [quotientTensorScalarExtensionMap, ModuleCat.comp_apply]
  erw [ModuleCat.extendScalars_δ_tmul]
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul]
  change quotientAlgebraScalarExtensionEquiv I S ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk I] s) ⊗ₜ[Q]
      quotientAlgebraScalarExtensionEquiv I T ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk I] t) = _
  rw [quotientAlgebraScalarExtensionEquiv_one_tmul,
    quotientAlgebraScalarExtensionEquiv_one_tmul]

set_option maxHeartbeats 800000 in
-- This compares the original quotient-ring and bundled scalar-extension tensor instances.
/-- The original derived tensor quotient iso retains the standard tensor augmentation. -/
lemma derivedTensorQuotientAlgebraIso_augmentation
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) :
    (derivedTensorQuotientAlgebraIso I S T hS hT).hom.hom ≫
        (boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of Q SQ)).app
          (ModuleCat.of Q TQ) =
      ((boundedAboveDerivedBaseChange (q)).map
        (ObjectProperty.homMk
          ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app
            (ModuleCat.of R T)))).hom ≫
        (boundedAboveDerivedBaseChangeModuleAugmentation (q)).app
          (ModuleCat.of R (S ⊗[R] T)) ≫
        (DerivedCategory.singleFunctor (ModuleCat Q) 0).map
          (quotientTensorScalarExtensionMap I S T) := by
  let M := ModuleCat.of R S
  let N := ModuleCat.of R T
  let F := ModuleCat.extendScalars (q)
  let eS : F.obj M ≅ ModuleCat.of Q SQ := (quotientAlgebraScalarExtensionEquiv I S).toModuleIso
  let eT : F.obj N ≅ ModuleCat.of Q TQ := (quotientAlgebraScalarExtensionEquiv I T).toModuleIso
  let βS : (boundedAboveDerivedBaseChange (q)).obj (boundedAboveDerivedSingleFunctor.obj M) ⟶
      boundedAboveDerivedSingleFunctor.obj (F.obj M) :=
    (boundedAboveDerivedBaseChangeModuleAugmentationIso (q) M hS).hom
  let βT : (boundedAboveDerivedBaseChange (q)).obj (boundedAboveDerivedSingleFunctor.obj N) ⟶
      boundedAboveDerivedSingleFunctor.obj (F.obj N) :=
    (boundedAboveDerivedBaseChangeModuleAugmentationIso (q) N hT).hom
  let fS : boundedAboveDerivedSingleFunctor.obj (F.obj M) ⟶
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q SQ) :=
    boundedAboveDerivedSingleFunctor.map eS.hom
  let fT : boundedAboveDerivedSingleFunctor.obj (F.obj N) ⟶
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q TQ) :=
    boundedAboveDerivedSingleFunctor.map eT.hom
  have hc :
      (derivedTensorQuotientAlgebraIso I S T hS hT).hom.hom =
        (boundedAboveDerivedTensorBaseChangeModuleIso (q) M N hS hT).hom.hom ≫
          (boundedAboveDerivedTensor.map (fS, fT)).hom := by
    have hcomp := boundedAboveDerivedTensor.map_comp
      (CategoryTheory.Prod.mkHom βS βT) (CategoryTheory.Prod.mkHom fS fT)
    have hc0 := congrArg (fun t =>
      (boundedAboveDerivedTensorBaseChangeIso (q)
        (boundedAboveDerivedSingleFunctor.obj M)
        (boundedAboveDerivedSingleFunctor.obj N)).hom.hom ≫ t.hom) hcomp
    simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc] at hc0
    simpa only [derivedTensorQuotientAlgebraIso, derivedQuotientAlgebraIso,
      boundedAboveDerivedTensorBaseChangeModuleIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.prod_hom, ObjectProperty.FullSubcategory.comp_hom, Category.assoc,
      CategoryTheory.prod_comp, M, N, F, eS, eT, βS, βT, fS, fT] using hc0
  have hn := boundedAboveDerivedTensorModuleAugmentation_naturality eS.hom eT.hom
  calc
    _ = (boundedAboveDerivedTensorBaseChangeModuleIso (q) M N hS hT).hom.hom ≫
        ((boundedAboveDerivedTensorModuleAugmentation (F.obj M)).app (F.obj N) ≫
          (DerivedCategory.singleFunctor (ModuleCat Q) 0).map (eS.hom ⊗ₘ eT.hom)) := by
      rw [hc, Category.assoc, hn]
    _ = (((boundedAboveDerivedBaseChange (q)).map
        (ObjectProperty.homMk ((boundedAboveDerivedTensorModuleAugmentation M).app N))).hom ≫
        (boundedAboveDerivedBaseChangeModuleAugmentation (q)).app (M ⊗ N) ≫
        (DerivedCategory.singleFunctor (ModuleCat Q) 0).map
          (Functor.OplaxMonoidal.δ F M N)) ≫
        (DerivedCategory.singleFunctor (ModuleCat Q) 0).map (eS.hom ⊗ₘ eT.hom) := by
      rw [← Category.assoc, boundedAboveDerivedTensorBaseChangeModuleIso_augmentation]
    _ = _ := by
      simp only [quotientTensorScalarExtensionMap, Functor.map_comp, Category.assoc]
      rfl

/-- The ordinary scalar-extension comparison is an isomorphism without a Tor hypothesis. -/
lemma quotientTensorScalarExtensionMap_isIso : IsIso (quotientTensorScalarExtensionMap I S T) := by
  unfold quotientTensorScalarExtensionMap
  infer_instance

/-- The original quotient tensor H⁰ map is the ordinary scalar-extension tensor comparison. -/
lemma derivedTensorQuotientAlgebraIso_homology
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T))
    (z : (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange (q)).obj
        (boundedAboveDerivedTensorAlgebra (R := R) S T).X).obj) :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ)
    letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ)
    derivedTensorH0AlgEquiv (R := Q) SQ TQ
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (derivedTensorQuotientAlgebraIso I S T hS hT).hom.hom z) =
      quotientTensorScalarExtensionMap I S T
        ((boundedAboveDerivedBaseChangeModuleH0Iso (q)).hom.app (ModuleCat.of R (S ⊗[R] T))
          ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
            (((boundedAboveDerivedBaseChange (q)).map
              (ObjectProperty.homMk
                ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app
                  (ModuleCat.of R T)))).hom) z)) := by
  let := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ)
  let := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ)
  let H0 := DerivedCategory.homologyFunctor (ModuleCat Q) 0
  let σ := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat Q) 0
  let B := ModuleCat.of R (S ⊗[R] T)
  let target := ModuleCat.of Q (SQ ⊗[Q] TQ)
  have h := congrArg (fun f => H0.map f ≫ σ.hom.app target)
    (derivedTensorQuotientAlgebraIso_augmentation I S T hS hT)
  simp only [Functor.map_comp, Category.assoc] at h
  have hn := σ.hom.naturality (quotientTensorScalarExtensionMap I S T)
  change H0.map ((DerivedCategory.singleFunctor (ModuleCat Q) 0).map
      (quotientTensorScalarExtensionMap I S T)) ≫ σ.hom.app target =
    σ.hom.app ((ModuleCat.extendScalars (q)).obj B) ≫ quotientTensorScalarExtensionMap I S T at hn
  rw [hn] at h
  have hb := boundedAboveDerivedBaseChangeModuleAugmentation_homology (q) B
  rw [realizedSingleH0Iso_hom_eq_standard] at hb
  rw [← Category.assoc (H0.map ((boundedAboveDerivedBaseChangeModuleAugmentation (q)).app B))
    (σ.hom.app ((ModuleCat.extendScalars (q)).obj B)), hb] at h
  have hz := congrArg (fun f => f z) h
  simp only [ModuleCat.comp_apply] at hz
  rw [derivedTensorH0AlgEquiv_apply, derivedTensorH0AlgHom_apply]
  exact hz

/-- With both factor Tor inputs, reduction of the original tensor augmentation is an H⁰ iso. -/
lemma derivedTensorQuotientAugmentation_h0_isIso
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
      (((boundedAboveDerivedBaseChange (q)).map
        (ObjectProperty.homMk
          (X := (boundedAboveDerivedTensorAlgebra (R := R) S T).X)
          (Y := (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)).X)
          ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app
            (ModuleCat.of R T)))).hom)) := by
  let A := boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ
  let := derivedH0CommRing A
  let := derivedH0Algebra A
  let H0 := DerivedCategory.homologyFunctor (ModuleCat Q) 0
  let e : H0.obj (A).X.obj ≃ₗ[Q] SQ ⊗[Q] TQ :=
    (derivedTensorH0AlgEquiv (R := Q) SQ TQ).toLinearEquiv
  let f := H0.map (((boundedAboveDerivedBaseChange (q)).map
    (ObjectProperty.homMk
          (X := (boundedAboveDerivedTensorAlgebra (R := R) S T).X)
          (Y := (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)).X)
      ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app
        (ModuleCat.of R T)))).hom)
  let b := (boundedAboveDerivedBaseChangeModuleH0Iso (q)).app (ModuleCat.of R (S ⊗[R] T))
  have h : f ≫ b.hom ≫ quotientTensorScalarExtensionMap I S T =
      H0.map (derivedTensorQuotientAlgebraIso I S T hS hT).hom.hom ≫ e.toModuleIso.hom := by
    ext z
    exact (derivedTensorQuotientAlgebraIso_homology I S T hS hT z).symm
  have : IsIso (f ≫ b.hom ≫ quotientTensorScalarExtensionMap I S T) := by
    rw [h]
    infer_instance
  let := quotientTensorScalarExtensionMap_isIso I S T
  exact IsIso.of_isIso_comp_right f (b.hom ≫ quotientTensorScalarExtensionMap I S T)

/-- Normalize the original reduced tensor by its own standard augmentation on H⁰. -/
def derivedTensorQuotientBaseChangeH0Iso
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) :
    (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        ((boundedAboveDerivedBaseChange (q)).obj
          (boundedAboveDerivedTensorAlgebra (R := R) S T).X).obj ≅
      (ModuleCat.extendScalars (q)).obj (ModuleCat.of R (S ⊗[R] T)) := by
  have := derivedTensorQuotientAugmentation_h0_isIso I S T hS hT
  exact asIso ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
      (((boundedAboveDerivedBaseChange (q)).map
        (ObjectProperty.homMk
          (X := (boundedAboveDerivedTensorAlgebra (R := R) S T).X)
          (Y := (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T)).X)
          ((boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R S)).app
            (ModuleCat.of R T)))).hom)) ≪≫
    (boundedAboveDerivedBaseChangeModuleH0Iso (q)).app (ModuleCat.of R (S ⊗[R] T))

/-- The original normalized class of s tensor t maps to the original two residue classes. -/
lemma derivedTensorQuotientAlgebraIso_homology_tmul
    (hS : scalarExtensionTorVanishing (q) (ModuleCat.of R S))
    (hT : scalarExtensionTorVanishing (q) (ModuleCat.of R T)) (s : S) (t : T) :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ)
    letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ)
    derivedTensorH0AlgEquiv (R := Q) SQ TQ
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).map
          (derivedTensorQuotientAlgebraIso I S T hS hT).hom.hom
          ((derivedTensorQuotientBaseChangeH0Iso I S T hS hT).inv
            ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk I] (s ⊗ₜ[R] t)))) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) s ⊗ₜ[Q]
        Ideal.Quotient.mk (I.map (algebraMap R T)) t := by
  let := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ)
  let := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := Q) SQ TQ)
  rw [derivedTensorQuotientAlgebraIso_homology]
  let e := derivedTensorQuotientBaseChangeH0Iso I S T hS hT
  change quotientTensorScalarExtensionMap I S T
    (e.hom (e.inv ((1 : Q) ⊗ₜ[R, Ideal.Quotient.mk I] (s ⊗ₜ[R] t)))) = _
  rw [ModuleCat.hom_inv_apply, quotientTensorScalarExtensionMap_one_tmul]

end SerrePositivity

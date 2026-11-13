import SerrePositivity.BhattScholze.Almost.AlmostTensorForward
import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedAcyclic
import SerrePositivity.BhattScholze.Perfectoidization.CompletedTensorComparison
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.RingTheory.TensorProduct.Quotient

noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Almost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open InfinityCategories DerivedCompletion MonoidalCategory
open scoped Simplicial TensorProduct
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (R : Type u) [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R']

def completeModuleBaseChange (X : DVertex R) : DVertex R' :=
  let F := (ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (.up ℤ)
  let Y := (derivedComplexCompletionFunctor R' (p : R')).obj
    (DerivedCategory.Q.obj (F.obj (X.obj 0).val))
  ((derivedInfinityHomotopyEquivalence R').inverse.obj Y).pt

def completeBaseChangeH0 : ModuleCat.{u} R ⥤ ModuleCat.{u} R' :=
  moduleFreeCochainResolution R ⋙ (ModuleCat.extendScalars (algebraMap R R')).mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q ⋙ derivedComplexCompletionFunctor R' (p : R') ⋙
    DerivedCategory.homologyFunctor (ModuleCat R') 0

private def completeBaseChangeH0ModelIso :
    boundedAboveDerivedSingleFunctor (R := R) ⋙ boundedAboveDerivedBaseChange (algebraMap R R') ⋙
      DerivedCategory.Minus.ι ⋙
        derivedComplexCompletionFunctor R' (algebraMap R R' (p : R)) ⋙
        DerivedCategory.homologyFunctor (ModuleCat R') 0 ≅
      completeBaseChangeH0 p R (R' := R') := by
  rw [map_natCast]
  let F := ModuleCat.extendScalars (algebraMap R R')
  let C := derivedComplexCompletionFunctor R' (p : R')
  let H := DerivedCategory.homologyFunctor (ModuleCat R') 0
  refine NatIso.ofComponents (fun M ↦ (C ⋙ H).mapIso
    (boundedAboveDerivedBaseChangeModelIso (algebraMap R R') _
      (moduleHeartProjectiveModel R M))) ?_
  intro M N f
  have h :
      DerivedCategory.Q.map ((moduleFreeCochainResolution R).map f) ≫
          (moduleHeartProjectiveModel R N).iso.hom =
        (moduleHeartProjectiveModel R M).iso.hom ≫ (boundedAboveDerivedSingleFunctor.map f).hom := by
    change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      (moduleFreeCochainAugmentationNat R).naturality]
  have h' := boundedAboveLeftDerivedModelIso_naturality F
    (moduleHeartProjectiveModel R M) (moduleHeartProjectiveModel R N)
    (boundedAboveDerivedSingleFunctor.map f) ((moduleFreeCochainResolution R).map f) h
  change (C ⋙ H).map _ ≫ (C ⋙ H).map _ = (C ⋙ H).map _ ≫ (C ⋙ H).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (C ⋙ H).map h'

private def baseChangeUnitDerivedIso :
    ((boundedAboveDerivedBaseChange (algebraMap R R')).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R))).obj ≅
    (moduleObjectFunctor R').obj (ModuleCat.of R' R') := by
  let F := ModuleCat.extendScalars (algebraMap R R')
  let e := boundedAboveDerivedBaseChangeModelIso (algebraMap R R')
    (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R)) boundedAboveDerivedTensorUnitModel
  exact e ≪≫ DerivedCategory.Q.mapIso
    (((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app (ModuleCat.of R R)) ≪≫
      (CochainComplex.singleFunctor (ModuleCat R') 0).mapIso (Functor.Monoidal.εIso F).symm)

variable [Fact p.Prime]

private def baseChangeUnitCompletedDerivedIso (hR' : IsIntegralPerfectoid R' p) :
    (derivedComplexCompletionFunctor R' (algebraMap R R' (p : R))).obj
      ((boundedAboveDerivedBaseChange (algebraMap R R')).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R R))).obj ≅
      (moduleObjectFunctor R').obj (ModuleCat.of R' R') := by
  let a := algebraMap R R' (p : R)
  have h : IsModuleComplete R' a (ModuleCat.of R' R') := by
    dsimp [a]
    simpa only [map_natCast] using hR'.isModuleComplete R' p
  exact (derivedComplexCompletionFunctor R' a).mapIso (baseChangeUnitDerivedIso R (R' := R')) ≪≫
    (derivedComplexCompletionUnitIso R' a _ h).symm

def completeBaseChangeUnitIso (hR' : IsIntegralPerfectoid R' p) :
    (completeBaseChangeH0 p R (R' := R')).obj (ModuleCat.of R R) ≅ ModuleCat.of R' R' :=
  ((completeBaseChangeH0ModelIso p R (R' := R')).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R') 0).mapIso
      (baseChangeUnitCompletedDerivedIso p R hR') ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R') 0).app _

#print axioms completeBaseChangeUnitIso



private def tensorQuotientBaseChange (J : Ideal R) :
    R' ⊗[R] (R ⧸ J) ≃ₐ[R'] R' ⧸ J.map (algebraMap R R') := by
  let e := Algebra.TensorProduct.rid R R' R'
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := R) R' R R' J).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change Ideal.map (algebraMap R R') J = Ideal.map e.toRingHom (Ideal.map
    (Algebra.TensorProduct.includeRight : R →ₐ[R] R' ⊗[R] R).toRingHom J)
  rw [Ideal.map_map]
  congr 1
  ext x
  change algebraMap R R' x = e ((1 : R') ⊗ₜ[R] x)
  simp [e, Algebra.smul_def]

variable (hR : IsIntegralPerfectoid R p) (J : Ideal R) (hR' : IsIntegralPerfectoid R' p)

private def quotientBaseChangeDerivedIso :
    (derivedComplexCompletionFunctor R' (p : R')).obj
      ((boundedAboveDerivedBaseChange (algebraMap R R')).obj
        (boundedAboveDerivedSingleFunctor.obj
          (ModuleCat.of R (QuotientPerfectoidization R J p hR)))).obj ≅
      (moduleObjectFunctor R').obj (ModuleCat.of R'
        (QuotientPerfectoidization R' (J.map (algebraMap R R')) p hR')) := by
  let J' := J.map (algebraMap R R')
  let B := QuotientPerfectoidization R J p hR
  let B' := QuotientPerfectoidization R' J' p hR'
  let f : R ⧸ J →ₐ[R] B :=
    { toRingHom := toQuotientPerfectoidization R J p hR
      commutes' := fun _ ↦ rfl }
  let f' : R' ⧸ J' →ₐ[R'] B' :=
    { toRingHom := toQuotientPerfectoidization R' J' p hR'
      commutes' := fun _ ↦ rfl }
  let e := tensorQuotientBaseChange R (R' := R') J
  let β := f'.comp e.toAlgHom
  have hβ : IsPerfectoidization p β.toRingHom :=
    (isPerfectoidization_toQuotientPerfectoidization R' J' p hR').comp_ringEquiv e.toRingEquiv
  rw [← map_natCast (algebraMap R R') p]
  exact targetCompletedBaseChangeIso R (R ⧸ J) R' B B' p hR hR' f
    (isPerfectoidization_toQuotientPerfectoidization R J p hR) β hβ

#print axioms quotientBaseChangeDerivedIso



end SerrePositivity.BhattScholze.Almost

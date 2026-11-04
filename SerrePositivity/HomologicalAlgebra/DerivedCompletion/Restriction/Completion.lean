module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Tower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionReflection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion

/-! # 完備化と任意の係数制限の可換性

## 概要

任意の係数の制限が実際の導来完備性を保ち、制限した元の完備化の単位が完備化の同値であることを示し、完備化が係数の制限と可換で元の単位を保つこと（`derivedCompletionRestrictionIso`）を与える。

## 方針

Koszul の段の準同型同値から完備化の同値を判定する。

## 規約

旧 `RestrictionComplete`・`RestrictionCompletionEquivalence`・`RestrictionCompletion`。

## 使われ方

BhattScholze、CLMST。
-/

@[expose] public noncomputable section

universe u

section RestrictionCompletePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (a : R)

/-- Restricting the original complete complex model gives an actually complete R-derived object. -/
lemma restrictedComplexCompletionObject_isComplete
    (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    IsComplete R a ((derivedRestrictScalars φ).obj (complexCompletionObject S (φ a) K)) := by
  let e : (derivedRestrictScalars φ).obj (complexCompletionObject S (φ a) K) ≅
      complexCompletionObject R a
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj K) :=
    (derivedRestrictScalarsFactors φ).app ((complexCompletionFunctor S (φ a)).obj K) ≪≫
      DerivedCategory.Q.mapIso (restrictionComplexCompletionIso φ a K)
  exact isComplete_of_iso R a e.symm (complexCompletionObject_isComplete R a _)

/-- The restricted actual S-completion is R-complete, for every unbounded derived source. -/
lemma restrictedDerivedCompletionObject_isComplete
    (X : ConcreteDerivedCategory S) :
    IsComplete R a ((derivedRestrictScalars φ).obj
      ((derivedComplexCompletionFunctor S (φ a)).obj X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : complexCompletionObject S (φ a) K ≅
      (derivedComplexCompletionFunctor S (φ a)).obj X :=
    (derivedComplexCompletionComparison S (φ a)).symm.app K ≪≫
      (derivedComplexCompletionFunctor S (φ a)).mapIso (DerivedCategory.Q.objObjPreimageIso X)
  exact isComplete_of_iso R a ((derivedRestrictScalars φ).mapIso e)
    (restrictedComplexCompletionObject_isComplete φ a K)

/-- Arbitrary coefficient restriction preserves the original derived completeness condition. -/
lemma derivedRestrictScalars_isComplete (X : ConcreteDerivedCategory S)
    (hX : IsComplete S (φ a) X) :
    IsComplete R a ((derivedRestrictScalars φ).obj X) :=
  isComplete_of_iso R a
    ((derivedRestrictScalars φ).mapIso (derivedComplexCompletionUnitIso S (φ a) X hX)).symm
    (restrictedDerivedCompletionObject_isComplete φ a X)

end SerrePositivity.DerivedCompletion

end RestrictionCompletePart

section RestrictionCompletionEquivalencePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (a : R)

/-- Every original Koszul quotient still inverts the restricted original S-completion unit. -/
lemma restrictionComplexCompletionUnit_koszul_quasiIso
    (K : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℕ) :
    QuasiIso ((scalarConeFunctor (a ^ n)).map
      (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        (complexCompletionUnit S (φ a) K))) := by
  have := complexCompletionUnit_koszul_quasiIso S (φ a) K n
  have hg : QuasiIso
      (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        ((scalarConeFunctor ((φ a) ^ n)).map (complexCompletionUnit S (φ a) K))) :=
    inferInstance
  have h := restrictionScalarConeIso_inv_naturality φ (a ^ n) ((φ a) ^ n)
    (map_pow φ a n) (complexCompletionUnit S (φ a) K)
  have hcomp : QuasiIso
      ((restrictionScalarConeIso φ (a ^ n) ((φ a) ^ n) (map_pow φ a n) K).inv ≫
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
          ((scalarConeFunctor ((φ a) ^ n)).map (complexCompletionUnit S (φ a) K))) :=
    inferInstance
  rw [h] at hcomp
  exact quasiIso_of_comp_right _
    (restrictionScalarConeIso φ (a ^ n) ((φ a) ^ n) (map_pow φ a n)
      ((complexCompletionFunctor S (φ a)).obj K)).inv

/-- Actual R-completion inverts the restricted original complex-level S-completion unit. -/
lemma restrictionComplexCompletionUnit_completion_quasiIso
    (K : CochainComplex (ModuleCat.{u} S) ℤ) :
    QuasiIso ((complexCompletionFunctor R a).map
      (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        (complexCompletionUnit S (φ a) K))) :=
  complexCompletionFunctor_map_quasiIso_of_koszul R a _
    (restrictionComplexCompletionUnit_koszul_quasiIso φ a K)

/-- In the actual derived category, R-completion inverts the restricted original S-unit. -/
lemma derivedRestrictionCompletionUnit_map_isIso
    (X : ConcreteDerivedCategory S) :
    IsIso ((derivedComplexCompletionFunctor R a).map
      ((derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).app X))) := by
  let F := derivedComplexCompletionFunctor R a
  let G := derivedRestrictScalars φ
  have hQ (K : CochainComplex (ModuleCat.{u} S) ℤ) :
      IsIso (F.map (G.map ((derivedComplexCompletionUnit S (φ a)).app
        (DerivedCategory.Q.obj K)))) := by
    let f := complexCompletionUnit S (φ a) K
    have := restrictionComplexCompletionUnit_completion_quasiIso φ a K
    have hq : IsIso (F.map (DerivedCategory.Q.map
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map f))) :=
      (NatIso.isIso_map_iff (derivedComplexCompletionComparison R a)
        (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map f)).mpr (by
          change IsIso (DerivedCategory.Q.map ((complexCompletionFunctor R a).map _))
          infer_instance)
    have hq' : IsIso (F.map (G.map (DerivedCategory.Q.map f))) :=
      (NatIso.isIso_map_iff
        (Functor.isoWhiskerRight (derivedRestrictScalarsFactors φ) F) f).mpr hq
    have hn := congrArg (fun g ↦ F.map (G.map g))
      (derivedComplexCompletionUnit_comparison S (φ a) K)
    simp only [CategoryTheory.Functor.map_comp] at hn
    have : IsIso (F.map (G.map ((derivedComplexCompletionUnit S (φ a)).app
        (DerivedCategory.Q.obj K))) ≫
        F.map (G.map ((derivedComplexCompletionComparison S (φ a)).hom.app K))) := by
      rw [hn]
      exact hq'
    exact IsIso.of_isIso_comp_right _
      (F.map (G.map ((derivedComplexCompletionComparison S (φ a)).hom.app K)))
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  have := hQ K
  have hn := congrArg (fun g ↦ F.map (G.map g))
    ((derivedComplexCompletionUnit S (φ a)).naturality e.hom)
  simp only [CategoryTheory.Functor.id_map, CategoryTheory.Functor.map_comp] at hn
  have : IsIso (F.map (G.map e.hom) ≫
      F.map (G.map ((derivedComplexCompletionUnit S (φ a)).app X))) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map (G.map e.hom)) _

end SerrePositivity.DerivedCompletion

end RestrictionCompletionEquivalencePart

section RestrictionCompletionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (a : R)

/-- Extend the restricted original S-completion unit by the original R-completion reflection. -/
def derivedCompletionRestrictionComparison (X : ConcreteDerivedCategory S) :
    (derivedComplexCompletionFunctor R a).obj ((derivedRestrictScalars φ).obj X) ⟶
      (derivedRestrictScalars φ).obj ((derivedComplexCompletionFunctor S (φ a)).obj X) :=
  (derivedComplexCompletionFunctor R a).map
      ((derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).app X)) ≫
    (derivedComplexCompletionUnitIso R a _
      (restrictedDerivedCompletionObject_isComplete φ a X)).inv

/-- The comparison preserves the original actual completion units exactly. -/
@[reassoc] lemma derivedCompletionRestrictionComparison_unit
    (X : ConcreteDerivedCategory S) :
    (derivedComplexCompletionUnit R a).app ((derivedRestrictScalars φ).obj X) ≫
        derivedCompletionRestrictionComparison φ a X =
      (derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).app X) :=
  (derivedComplexCompletionHomEquiv R a _ _
    (restrictedDerivedCompletionObject_isComplete φ a X)).apply_symm_apply _

/-- The canonical unit-normalized comparison is always an isomorphism. -/
lemma derivedCompletionRestrictionComparison_isIso (X : ConcreteDerivedCategory S) :
    IsIso (derivedCompletionRestrictionComparison φ a X) := by
  dsimp only [derivedCompletionRestrictionComparison]
  have := derivedRestrictionCompletionUnit_map_isIso φ a X
  infer_instance

/-- Reflection uniqueness makes the actual comparisons natural in every derived morphism. -/
lemma derivedCompletionRestrictionComparison_naturality
    {X Y : ConcreteDerivedCategory S} (f : X ⟶ Y) :
    (derivedComplexCompletionFunctor R a).map ((derivedRestrictScalars φ).map f) ≫
        derivedCompletionRestrictionComparison φ a Y =
      derivedCompletionRestrictionComparison φ a X ≫
        (derivedRestrictScalars φ).map ((derivedComplexCompletionFunctor S (φ a)).map f) := by
  apply derivedComplexCompletionHom_ext R a (restrictedDerivedCompletionObject_isComplete φ a Y)
  have hr := (derivedComplexCompletionUnit R a).naturality ((derivedRestrictScalars φ).map f)
  simp only [CategoryTheory.Functor.id_map] at hr
  rw [← Category.assoc, ← hr, Category.assoc, derivedCompletionRestrictionComparison_unit,
    ← Category.assoc, derivedCompletionRestrictionComparison_unit,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  simpa only [CategoryTheory.Functor.id_map] using
    congrArg (derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).naturality f)

/-- Arbitrary restriction commutes naturally with the actual derived completion functors. -/
def derivedCompletionRestrictionIso :
    derivedRestrictScalars φ ⋙ derivedComplexCompletionFunctor R a ≅
      derivedComplexCompletionFunctor S (φ a) ⋙ derivedRestrictScalars φ :=
  NatIso.ofComponents
    (F := derivedRestrictScalars φ ⋙ derivedComplexCompletionFunctor R a)
    (G := derivedComplexCompletionFunctor S (φ a) ⋙ derivedRestrictScalars φ)
    (fun X ↦ by
    have := derivedCompletionRestrictionComparison_isIso φ a X
    exact asIso (derivedCompletionRestrictionComparison φ a X))
    (fun {X Y} f ↦ by
      change (derivedComplexCompletionFunctor R a).map ((derivedRestrictScalars φ).map f) ≫
        derivedCompletionRestrictionComparison φ a Y = _
      exact derivedCompletionRestrictionComparison_naturality φ a f)

/-- The natural isomorphism, with the original standard units, satisfies the required diagram. -/
@[reassoc] lemma derivedCompletionRestrictionIso_unit (X : ConcreteDerivedCategory S) :
    (derivedComplexCompletionUnit R a).app ((derivedRestrictScalars φ).obj X) ≫
        (derivedCompletionRestrictionIso φ a).hom.app X =
      (derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).app X) :=
  derivedCompletionRestrictionComparison_unit φ a X

/-- In the reverse orientation the original restricted unit is sent to the original R-unit. -/
@[reassoc] lemma derivedCompletionRestrictionIso_inv_unit (X : ConcreteDerivedCategory S) :
    (derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).app X) ≫
        (derivedCompletionRestrictionIso φ a).inv.app X =
      (derivedComplexCompletionUnit R a).app ((derivedRestrictScalars φ).obj X) := by
  rw [← derivedCompletionRestrictionIso_unit φ a X, Category.assoc,
    Iso.hom_inv_id_app]
  erw [Category.comp_id]

/-- The same actual natural comparison is available in the standard bounded-above categories. -/
def boundedAboveCompletionRestrictionIso :
    boundedAboveDerivedRestrictScalars φ ⋙ boundedAboveDerivedCompletionFunctor R a ≅
      boundedAboveDerivedCompletionFunctor S (φ a) ⋙ boundedAboveDerivedRestrictScalars φ :=
  NatIso.ofComponents
    (F := boundedAboveDerivedRestrictScalars φ ⋙ boundedAboveDerivedCompletionFunctor R a)
    (G := boundedAboveDerivedCompletionFunctor S (φ a) ⋙ boundedAboveDerivedRestrictScalars φ)
    (fun X ↦ ObjectProperty.isoMk _ ((derivedCompletionRestrictionIso φ a).app X.obj))
    (fun {X Y} f ↦ by
      apply InducedCategory.hom_ext
      exact (derivedCompletionRestrictionIso φ a).hom.naturality f.hom)

/-- The bounded-above comparison preserves the original units in the bounded categories. -/
@[reassoc] lemma boundedAboveCompletionRestrictionIso_unit
    (X : DerivedCategory.Minus (ModuleCat.{u} S)) :
    (boundedAboveDerivedCompletionUnit R a).app ((boundedAboveDerivedRestrictScalars φ).obj X) ≫
        (boundedAboveCompletionRestrictionIso φ a).hom.app X =
      (boundedAboveDerivedRestrictScalars φ).map
        ((boundedAboveDerivedCompletionUnit S (φ a)).app X) := by
  apply InducedCategory.hom_ext
  exact derivedCompletionRestrictionIso_unit φ a X.obj

/-- The requested G8 orientation: complete and restrict, or restrict and complete. -/
def derivedRestrictionCompletionIso :
    derivedComplexCompletionFunctor S (φ a) ⋙ derivedRestrictScalars φ ≅
      derivedRestrictScalars φ ⋙ derivedComplexCompletionFunctor R a :=
  (derivedCompletionRestrictionIso φ a).symm

/-- The G8-oriented isomorphism preserves exactly the original standard units. -/
@[reassoc] lemma derivedRestrictionCompletionIso_unit (X : ConcreteDerivedCategory S) :
    (derivedRestrictScalars φ).map ((derivedComplexCompletionUnit S (φ a)).app X) ≫
        (derivedRestrictionCompletionIso φ a).hom.app X =
      (derivedComplexCompletionUnit R a).app ((derivedRestrictScalars φ).obj X) :=
  derivedCompletionRestrictionIso_inv_unit φ a X

end SerrePositivity.DerivedCompletion

end RestrictionCompletionPart

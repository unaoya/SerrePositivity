module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionReflection

/-! # The restricted original completion unit is an actual completion equivalence -/
@[expose] public noncomputable section
universe u
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

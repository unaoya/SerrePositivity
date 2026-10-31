module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletionHomologyComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DivisibleHomZero
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
/-! # Purity detected by a discrete Koszul reduction

Derived completeness and degree-zero concentration of the scalar cone force the
original object to be discrete, with injective scalar action on its H0.
There is no flatness, finiteness, boundedness, or ring regularity assumption in
this Koszul criterion. The ordinary quotient variant requires regularity of a on R.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R)

/-- A complete module on which the completion scalar is surjective is zero. -/
lemma isZero_of_complete_of_smul_surjective (M : ModuleCat.{u} R)
    (hc : IsModuleComplete R a M) (hs : Function.Surjective (fun x : M => a • x)) :
    IsZero M := by
  have h := linearMap_eq_zero_of_smul_surjective_of_isModuleComplete a M M hs hc
    (LinearMap.id : M →ₗ[R] M)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  exact congrArg (fun f : M →ₗ[R] M => f x) h

/-- Vanishing of scalar-cone homology gives surjectivity on the original homology. -/
lemma cochain_homology_smul_surjective_of_scalarCone_isZero
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (h : IsZero (((scalarConeFunctor a).obj K).homology i)) :
    Function.Surjective (fun x : K.homology i => a • x) := by
  have he := Cone.exact₂ (smulId a K) i
  have hm : Epi (homologyMap (smulId a K) i) :=
    he.epi_f (h.eq_zero_of_tgt _)
  have hs := (ModuleCat.epi_iff_surjective _).mp hm
  simp only [smulId, homologyMap_smul, homologyMap_id] at hs
  exact hs

/-- Vanishing in the previous scalar-cone degree gives injectivity on homology. -/
lemma cochain_homology_smul_injective_of_scalarCone_isZero
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (h : IsZero (((scalarConeFunctor a).obj K).homology (i - 1))) :
    Function.Injective (fun x : K.homology i => a • x) := by
  have he := Cone.exact₁ (smulId a K) (i - 1) i (by omega)
  have hm : Mono (homologyMap (smulId a K) i) :=
    he.mono_g (h.eq_zero_of_src _)
  have hs := (ModuleCat.mono_iff_injective _).mp hm
  simp only [smulId, homologyMap_smul, homologyMap_id] at hs
  exact hs

/-- The surjectivity statement on the original actual derived homology. -/
lemma derived_homology_smul_surjective_of_scalarCone_isZero
    (X : ConcreteDerivedCategory R) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj X))) :
    Function.Surjective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X => a • x) := by
  let K := DerivedCategory.Q.objPreimage X
  let eX := DerivedCategory.Q.objObjPreimageIso X
  let eH : K.homology i ≅ (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso eX
  let ec := ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app
      ((scalarConeFunctor a).obj K)).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      ((derivedScalarConeComparison R a).symm.app K ≪≫
        (derivedScalarConeFunctor R a).mapIso eX)
  have hs := cochain_homology_smul_surjective_of_scalarCone_isZero a K i (h.of_iso ec)
  intro x
  obtain ⟨y, hy⟩ := hs (eH.toLinearEquiv.symm x)
  refine ⟨eH.toLinearEquiv y, ?_⟩
  change a • eH.toLinearEquiv y = x
  change a • y = eH.toLinearEquiv.symm x at hy
  rw [← eH.toLinearEquiv.map_smul, hy, eH.toLinearEquiv.apply_symm_apply]

/-- The injectivity statement on the original actual derived homology. -/
lemma derived_homology_smul_injective_of_scalarCone_isZero
    (X : ConcreteDerivedCategory R) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (i - 1)).obj
      ((derivedScalarConeFunctor R a).obj X))) :
    Function.Injective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X => a • x) := by
  let K := DerivedCategory.Q.objPreimage X
  let eX := DerivedCategory.Q.objObjPreimageIso X
  let eH : K.homology i ≅ (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso eX
  let ec := ((DerivedCategory.homologyFunctorFactors (ModuleCat R) (i - 1)).app
      ((scalarConeFunctor a).obj K)).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) (i - 1)).mapIso
      ((derivedScalarConeComparison R a).symm.app K ≪≫
        (derivedScalarConeFunctor R a).mapIso eX)
  have hs := cochain_homology_smul_injective_of_scalarCone_isZero a K i (h.of_iso ec)
  intro x y hxy
  apply eH.toLinearEquiv.symm.injective
  apply hs
  change a • eH.toLinearEquiv.symm x = a • eH.toLinearEquiv.symm y
  change a • x = a • y at hxy
  rw [← eH.toLinearEquiv.symm.map_smul, ← eH.toLinearEquiv.symm.map_smul, hxy]

/-- A complete homology module vanishes when the same scalar-cone homology vanishes. -/
lemma derived_homology_isZero_of_complete_of_scalarCone_isZero
    (X : ConcreteDerivedCategory R) (hc : IsComplete R a X) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj X))) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X) :=
  isZero_of_complete_of_smul_surjective a _ (isComplete_homology_isModuleComplete R a X hc i)
    (derived_homology_smul_surjective_of_scalarCone_isZero a X i h)

/-- A complete object with discrete Koszul reduction is discrete, with regular H0 action. -/
lemma derived_pure_of_complete_scalarCone_pure
    (X : ConcreteDerivedCategory R) (hc : IsComplete R a X)
    (h : ∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj X))) :
    X.IsGE 0 ∧ X.IsLE 0 ∧
      Function.Injective
        (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X => a • x) := by
  have hz (i : ℤ) (hi : i ≠ 0) :=
    derived_homology_isZero_of_complete_of_scalarCone_isZero a X hc i (h i hi)
  exact ⟨(DerivedCategory.isGE_iff _ _).mpr (fun i hi => hz i (by omega)),
    (DerivedCategory.isLE_iff _ _).mpr (fun i hi => hz i (by omega)),
    derived_homology_smul_injective_of_scalarCone_isZero a X 0 (by simpa using h (-1) (by omega))⟩

/-- For a regular scalar on R, an ordinary derived quotient can detect the same purity. -/
lemma derived_pure_of_complete_regular_quotient_pure
    (ha : IsSMulRegular R a) (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hc : IsComplete R a X.obj)
    (h : ∀ i : ℤ, i ≠ 0 → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (R ⧸ Ideal.span {a})) i).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj X).obj)) :
    X.obj.IsGE 0 ∧ X.obj.IsLE 0 ∧
      Function.Injective
        (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj X.obj => a • x) := by
  apply derived_pure_of_complete_scalarCone_pure a X.obj hc
  intro i hi
  let q := Ideal.Quotient.mk (Ideal.span {a})
  let Y := (boundedAboveDerivedBaseChange q).obj X
  let e := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      (restrictedDerivedQuotientKoszulIso a ha X).symm ≪≫
    (derivedRestrictScalarsHomologyIso q i).app Y.obj
  exact ((ModuleCat.restrictScalars q).map_isZero (h i hi)).of_iso e
end SerrePositivity.DerivedCompletion

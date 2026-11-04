module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Reconstruction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel

/-! # 一つの座標の完備化の導来比較と関手性

## 概要

完備化した単位の代数を元の主元 Koszul の H⁰ 環と比べ（`principalCompletedUnitH0Iso`）、環準同型・環同型に沿った一つの座標の完備化の射（`principalCompletionMap`・`principalCompletionRingEquiv`）と単位の保存を与える。

## 方針

始域と終域は元の Koszul 完備化の H⁰ 環。射は一意存在から作る（2b の B で持ち上げの def にする候補）。

## 規約

スカラーの正則性や有界ねじれは仮定しない。旧 `PrincipalCompletionDerivedComparison`・`PrincipalCompletionFunctor`。

## 使われ方

`CompletedAlgebraH0`、BhattScholze。
-/

@[expose] public noncomputable section

universe u

section PrincipalCompletionDerivedComparisonPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)

/-- On the coefficient ring in degree zero, the original two completion complexes coincide. -/
lemma complexCompletion_single_eq_koszul :
    (complexCompletionFunctor R a).obj
      ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) =
      koszulCompletionComplex R (fun _ : Fin 1 ↦ a) := rfl

/-- This equality also preserves the original complex-level completion unit. -/
lemma complexCompletion_single_unit_eq_koszul :
    complexCompletionUnit R a
      ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) =
      koszulCompletionUnit R (fun _ : Fin 1 ↦ a) := by
  have hh (n : ℕ) : koszulComplexInclusion R (fun _ : Fin 1 ↦ a ^ n) =
      CochainComplex.mappingCone.inr (smulId (a ^ n)
        ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))) := by
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  simp only [complexCompletionUnit, koszulCompletionUnit, hh]
  rfl

/-- The actual commutative algebra obtained by completing the coefficient ring in degree zero. -/
abbrev completedUnitAlgebra :=
  (boundedAboveCompletionCommMonFunctor R a).obj (boundedAboveDerivedAlgebra (R := R) R)

/-- Compare actual H⁰ to the original principal Koszul complex using the original Q factors. -/
def principalCompletedUnitH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (completedUnitAlgebra R a).X.obj ≅
      (koszulCompletionComplex R (fun _ : Fin 1 ↦ a)).homology 0 :=
  (DerivedCategory.homologyFunctor (ModuleCat R) 0).mapIso
      ((derivedComplexCompletionComparison R a).app
        ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).app
      ((complexCompletionFunctor R a).obj
        ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)))

/-- The comparison preserves the original standard map from every coefficient. -/
lemma principalCompletedUnitH0Iso_unit (r : R) :
    (principalCompletedUnitH0Iso R a).hom
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) R))
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R R) r)) = koszulCompletionH0Unit R (fun _ : Fin 1 ↦ a) r := by
  rw [completionH0AlgebraUnit_apply]
  change ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
      (ModuleCat.of R R) ≫
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((derivedComplexCompletionUnit R a).app
        (DerivedCategory.Q.obj (cochainTensorUnit (R := R)))) ≫
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((derivedComplexCompletionComparison R a).hom.app (cochainTensorUnit (R := R))) ≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).hom.app
      ((complexCompletionFunctor R a).obj (cochainTensorUnit (R := R)))).hom r = _
  have h : (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
      (ModuleCat.of R R) ≫
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((derivedComplexCompletionUnit R a).app
        (DerivedCategory.Q.obj (cochainTensorUnit (R := R)))) ≫
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      ((derivedComplexCompletionComparison R a).hom.app (cochainTensorUnit (R := R))) ≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).hom.app
      ((complexCompletionFunctor R a).obj (cochainTensorUnit (R := R))) =
      ModuleCat.ofHom (koszulCompletionH0Unit R (fun _ : Fin 1 ↦ a)) := by
    rw [← CategoryTheory.Functor.map_comp_assoc, derivedComplexCompletionUnit_comparison]
    change _ ≫ (DerivedCategory.homologyFunctor (ModuleCat R) 0).map
      (DerivedCategory.Q.map (complexCompletionUnit R a (cochainTensorUnit (R := R)))) ≫ _ = _
    rw [DerivedCategory.homologyFunctorFactors_hom_naturality, ← Category.assoc]
    erw [derivedSingleH0Iso_inv_factors]
    erw [complexCompletion_single_unit_eq_koszul]
    rfl
  exact congrArg (fun f ↦ f.hom r) h

/-- The completed unit algebra uses the original completion unit as its algebra unit. -/
lemma completedUnitAlgebra_one_eq_unit :
    (completedUnitAlgebra R a).mon.one =
      (boundedAboveCompletionAlgebraUnit R a (boundedAboveDerivedAlgebra (R := R) R)).hom.hom := by
  rw [boundedAboveCompletionAlgebraUnit_hom]
  change ((boundedAboveCompletionCommMonFunctor R a).obj
    (boundedAboveDerivedAlgebra (R := R) R)).mon.one = _
  rw [boundedAboveCompletionCommMonFunctor_one]
  have hu : (boundedAboveDerivedAlgebra (R := R) R).mon.one =
      𝟙 (𝟙_ (DerivedCategory.Minus (ModuleCat R))) := by
    apply InducedCategory.hom_ext
    change (𝟙 _) ≫ (DerivedCategory.singleFunctor (ModuleCat R) 0).map
      (ModuleCat.ofHom (Algebra.linearMap R R)) = 𝟙 _
    have hf : ModuleCat.ofHom (Algebra.linearMap R R) = 𝟙 (ModuleCat.of R R) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      simp
    rw [hf, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hu, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- The actual H⁰ ring unit is the distinguished unit of the original Koszul reflection. -/
lemma principalCompletedUnitH0Iso_one :
    letI := derivedH0CommRing (completedUnitAlgebra R a)
    (principalCompletedUnitH0Iso R a).hom
      (1 : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (completedUnitAlgebra R a).X.obj) =
      koszulCompletionH0Unit R (fun _ : Fin 1 ↦ a) 1 := by
  let := derivedH0CommRing (completedUnitAlgebra R a)
  rw [derivedH0_one_standard, completedUnitAlgebra_one_eq_unit]
  have h := principalCompletedUnitH0Iso_unit R a 1
  rw [derivedH0AlgMap_apply] at h
  exact h

/-- The actual completed coefficient algebra is the original principal Koszul H⁰ algebra. -/
def principalCompletedUnitH0AlgEquiv :
    letI := derivedH0CommRing (completedUnitAlgebra R a)
    letI := derivedH0Algebra (completedUnitAlgebra R a)
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (completedUnitAlgebra R a).X.obj ≃ₐ[R]
      PrincipalCompletionH0 R a := by
  letI := derivedH0CommRing (completedUnitAlgebra R a)
  letI := derivedH0Algebra (completedUnitAlgebra R a)
  letI := principalCompletionCommRing R a
  letI := principalCompletionAlgebra R a
  let E := (principalCompletedUnitH0Iso R a).toLinearEquiv
  let h := principalCompletionH0_isCompleteModuleReflection R a
  have hT : ∀ j : Fin 1, IsModuleComplete R a
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (completedUnitAlgebra R a).X.obj) := by
    intro j
    exact derivedComplexCompletionFunctor_homology_isModuleComplete R a
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R)) 0
  have h1 : E.symm (koszulCompletionH0Unit R (fun _ : Fin 1 ↦ a) 1) = 1 := by
    apply E.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (principalCompletedUnitH0Iso_one R a).symm
  exact (AlgEquiv.ofLinearEquiv E.symm h1
    (h.linearMap_map_mul _ hT E.symm.toLinearMap h1)).symm

/-- Its function remains the standard derived-to-Koszul H⁰ comparison. -/
lemma principalCompletedUnitH0AlgEquiv_apply
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (completedUnitAlgebra R a).X.obj) :
    letI := derivedH0CommRing (completedUnitAlgebra R a)
    letI := derivedH0Algebra (completedUnitAlgebra R a)
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    principalCompletedUnitH0AlgEquiv R a x = (principalCompletedUnitH0Iso R a).hom x := rfl

/-- The algebra comparison preserves the original standard ring completion map. -/
lemma principalCompletedUnitH0AlgEquiv_unit (r : R) :
    letI := derivedH0CommRing (completedUnitAlgebra R a)
    letI := derivedH0Algebra (completedUnitAlgebra R a)
    letI := principalCompletionCommRing R a
    letI := principalCompletionAlgebra R a
    principalCompletedUnitH0AlgEquiv R a
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedAlgebra (R := R) R))
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).inv.app
          (ModuleCat.of R R) r)) = principalCompletionUnitRingHom R a r := by
  rw [principalCompletedUnitH0AlgEquiv_apply, principalCompletedUnitH0Iso_unit,
    principalCompletionUnitRingHom_apply]

end SerrePositivity.DerivedCompletion

end PrincipalCompletionDerivedComparisonPart

section PrincipalCompletionFunctorPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The actual completion is complete for the action of its original ring unit. -/
lemma principalCompletion_isModuleComplete_unit (a : R) :
    letI := principalCompletionCommRing R a
    letI := (principalCompletionUnitRingHom R a).toAlgebra
    letI : Module R (PrincipalCompletionH0 R a) := Algebra.toModule
    IsModuleComplete R a (ModuleCat.of R (PrincipalCompletionH0 R a)) := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionAlgebra R a
  have h := principalCompletionH0_isModuleComplete R a
  rw [isModuleComplete_iff_recurrence_bijective] at h ⊢
  convert h using 1
  funext x n
  exact congrArg (fun z : PrincipalCompletionH0 R a => x n - z)
    ((principalCompletionH0_isCompleteModuleReflection R a).mul_scalar_unit a (x (n + 1)))

/-- Completeness after restricting through the original target completion unit. -/
lemma principalCompletion_isModuleComplete_comp
    (φ : R →+* S) (a : R) (b : S) (hab : φ a = b) :
    letI := principalCompletionCommRing S b
    letI := ((principalCompletionUnitRingHom S b).comp φ).toAlgebra
    letI : Module R (PrincipalCompletionH0 S b) := Algebra.toModule
    IsModuleComplete R a (ModuleCat.of R (PrincipalCompletionH0 S b)) := by
  letI := principalCompletionCommRing S b
  apply (isModuleComplete_ringHom_comp_iff R S _ φ
    (principalCompletionUnitRingHom S b) a).mp
  rw [hab]
  exact principalCompletion_isModuleComplete_unit b

/-- Transport the original principal completion along a ring map carrying a to b. -/
def principalCompletionMap (φ : R →+* S) (a : R) (b : S) (hab : φ a = b) :
    letI := principalCompletionCommRing R a
    letI := principalCompletionCommRing S b
    PrincipalCompletionH0 R a →+* PrincipalCompletionH0 S b := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionCommRing S b
  exact principalCompletionLift R a _ ((principalCompletionUnitRingHom S b).comp φ)
    (principalCompletion_isModuleComplete_comp φ a b hab)

/-- The induced map retains the original completion-unit square. -/
lemma principalCompletionMap_comp (φ : R →+* S) (a : R) (b : S) (hab : φ a = b) :
    letI := principalCompletionCommRing R a
    letI := principalCompletionCommRing S b
    (principalCompletionMap φ a b hab).comp (principalCompletionUnitRingHom R a) =
      (principalCompletionUnitRingHom S b).comp φ := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionCommRing S b
  exact principalCompletionLift_comp R a _ ((principalCompletionUnitRingHom S b).comp φ)
    (principalCompletion_isModuleComplete_comp φ a b hab)

/-- Ring equivalences induce ring equivalences of the actual principal completions. -/
def principalCompletionRingEquiv (e : R ≃+* S) (a : R) (b : S) (hab : e a = b) :
    letI := principalCompletionCommRing R a
    letI := principalCompletionCommRing S b
    PrincipalCompletionH0 R a ≃+* PrincipalCompletionH0 S b := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionCommRing S b
  have hba : e.symm b = a := by rw [← hab, e.symm_apply_apply]
  let F := principalCompletionMap e.toRingHom a b hab
  let G := principalCompletionMap e.symm.toRingHom b a hba
  have hGF : (G.comp F).comp (principalCompletionUnitRingHom R a) =
      principalCompletionUnitRingHom R a := by
    rw [RingHom.comp_assoc, principalCompletionMap_comp, ← RingHom.comp_assoc,
      principalCompletionMap_comp]
    ext x
    simp
  have hFG : (F.comp G).comp (principalCompletionUnitRingHom S b) =
      principalCompletionUnitRingHom S b := by
    rw [RingHom.comp_assoc, principalCompletionMap_comp, ← RingHom.comp_assoc,
      principalCompletionMap_comp]
    ext x
    simp
  have hGFid : G.comp F = RingHom.id _ :=
    (principalCompletion_existsUnique_ringHom R a _ (principalCompletionUnitRingHom R a)
      (principalCompletion_isModuleComplete_unit a)).unique hGF (RingHom.id_comp _)
  have hFGid : F.comp G = RingHom.id _ :=
    (principalCompletion_existsUnique_ringHom S b _ (principalCompletionUnitRingHom S b)
      (principalCompletion_isModuleComplete_unit b)).unique hFG (RingHom.id_comp _)
  exact
    { F with
      invFun := G
      left_inv := fun x => RingHom.congr_fun hGFid x
      right_inv := fun x => RingHom.congr_fun hFGid x }

/-- The equivalence uses the same original ring map on every unit representative. -/
@[simp] lemma principalCompletionRingEquiv_unit
    (e : R ≃+* S) (a : R) (b : S) (hab : e a = b) (x : R) :
    letI := principalCompletionCommRing R a
    letI := principalCompletionCommRing S b
    principalCompletionRingEquiv e a b hab (principalCompletionUnitRingHom R a x) =
      principalCompletionUnitRingHom S b (e x) :=
  RingHom.congr_fun (principalCompletionMap_comp e.toRingHom a b hab) x

end SerrePositivity.DerivedCompletion

end PrincipalCompletionFunctorPart

module
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeScalar
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedHomologyLinear

/-! # The original target-scalar action after actual completed derived base change -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard

/-- The actual completion preserves scalar identity maps by uniqueness along its original unit. -/
lemma derivedCompletion_map_scalar_id (R : Type u) [CommRing R] (a : R)
    (X : ConcreteDerivedCategory R) (s : R) :
    (derivedComplexCompletionFunctor R a).map (s • 𝟙 X) =
      s • 𝟙 ((derivedComplexCompletionFunctor R a).obj X) := by
  apply derivedComplexCompletionHom_ext R a
    (derivedComplexCompletionFunctor_isComplete R a X)
  calc
    (derivedComplexCompletionUnit R a).app X ≫
        (derivedComplexCompletionFunctor R a).map (s • 𝟙 X) =
      (s • 𝟙 X) ≫ (derivedComplexCompletionUnit R a).app X :=
      ((derivedComplexCompletionUnit R a).naturality (s • 𝟙 X)).symm
    _ = s • (derivedComplexCompletionUnit R a).app X := by simp
    _ = (derivedComplexCompletionUnit R a).app X ≫
      (s • 𝟙 ((derivedComplexCompletionFunctor R a).obj X)) := by simp

lemma boundedAboveCompletion_map_scalar_id (R : Type u) [CommRing R] (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (s : R) :
    (boundedAboveDerivedCompletionFunctor R a).map (s • 𝟙 X) =
      s • 𝟙 ((boundedAboveDerivedCompletionFunctor R a).obj X) := by
  apply InducedCategory.hom_ext
  exact derivedCompletion_map_scalar_id R a X.obj s

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- Complete the original S-base change and restrict, or complete its original R-tensor model. -/
def completedBaseChangeTensorRestrictionIso (X : D) :
    (boundedAboveDerivedRestrictScalars φ).obj
        ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
          ((boundedAboveDerivedBaseChange φ).obj X)) ≅
      (boundedAboveDerivedCompletionFunctor R a).obj
        (boundedAboveDerivedTensor.obj (derivedBaseChangeScalarObject φ, X)) :=
  ((boundedAboveCompletionRestrictionIso φ a).app
    ((boundedAboveDerivedBaseChange φ).obj X)).symm ≪≫
      (boundedAboveDerivedCompletionFunctor R a).mapIso
        (boundedAboveDerivedBaseChangeTensorIso φ X)

/-- Every original S scalar becomes its completed original scalar-factor multiplication. -/
lemma completedBaseChangeTensorRestrictionIso_scalar (X : D) (s : S) :
    (boundedAboveDerivedRestrictScalars φ).map
        (s • 𝟙 ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
          ((boundedAboveDerivedBaseChange φ).obj X))) ≫
        (completedBaseChangeTensorRestrictionIso φ a X).hom =
      (completedBaseChangeTensorRestrictionIso φ a X).hom ≫
        (boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
          (CategoryTheory.Prod.mkHom
            (show derivedBaseChangeScalarObject φ ⟶ derivedBaseChangeScalarObject φ from
              boundedAboveDerivedSingleFunctor.map (restrictedScalarMultiplication φ s)) (𝟙 X))) := by
  have hn := (boundedAboveCompletionRestrictionIso φ a).inv.naturality
    (s • 𝟙 ((boundedAboveDerivedBaseChange φ).obj X))
  simp only [Functor.comp_map] at hn
  rw [boundedAboveCompletion_map_scalar_id] at hn
  change (boundedAboveDerivedRestrictScalars φ).map
      (s • 𝟙 ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
        ((boundedAboveDerivedBaseChange φ).obj X))) ≫
      ((boundedAboveCompletionRestrictionIso φ a).app
        ((boundedAboveDerivedBaseChange φ).obj X)).inv =
    ((boundedAboveCompletionRestrictionIso φ a).app
      ((boundedAboveDerivedBaseChange φ).obj X)).inv ≫
      (boundedAboveDerivedCompletionFunctor R a).map
        ((boundedAboveDerivedRestrictScalars φ).map
          (s • 𝟙 ((boundedAboveDerivedBaseChange φ).obj X))) at hn
  simp only [completedBaseChangeTensorRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, hn, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (boundedAboveDerivedCompletionFunctor R a).map
    (boundedAboveDerivedBaseChangeTensorIso_scalar φ X s)

/-- The actual homology comparison retains the original S module on its source. -/
def completedBaseChangeTensorRestrictionHomologyIso (X : D) (i : ℤ) :
    (ModuleCat.restrictScalars φ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj
          ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
            ((boundedAboveDerivedBaseChange φ).obj X)).obj) ≅
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        ((boundedAboveDerivedCompletionFunctor R a).obj
          (boundedAboveDerivedTensor.obj (derivedBaseChangeScalarObject φ, X))).obj :=
  ((derivedRestrictScalarsHomologyIso φ i).app
    ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
      ((boundedAboveDerivedBaseChange φ).obj X)).obj).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      (DerivedCategory.Minus.ι.mapIso (completedBaseChangeTensorRestrictionIso φ a X))

/-- At every actual homology degree the comparison intertwines every target scalar
with the original completed scalar-factor action. -/
lemma completedBaseChangeTensorRestrictionHomologyIso_scalar (X : D) (i : ℤ) (s : S)
    (x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
      ((boundedAboveDerivedCompletionFunctor S (φ a)).obj
        ((boundedAboveDerivedBaseChange φ).obj X)).obj) :
    (completedBaseChangeTensorRestrictionHomologyIso φ a X i).hom (s • x) =
      (DerivedCategory.homologyFunctor (ModuleCat R) i).map
        ((boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
          (CategoryTheory.Prod.mkHom
            (show derivedBaseChangeScalarObject φ ⟶ derivedBaseChangeScalarObject φ from
              boundedAboveDerivedSingleFunctor.map (restrictedScalarMultiplication φ s)) (𝟙 X)))).hom
        ((completedBaseChangeTensorRestrictionHomologyIso φ a X i).hom x) := by
  let Y := (boundedAboveDerivedCompletionFunctor S (φ a)).obj
    ((boundedAboveDerivedBaseChange φ).obj X)
  have hd := congrArg (DerivedCategory.homologyFunctor (ModuleCat R) i).map
    (congrArg (fun f => f.hom) (completedBaseChangeTensorRestrictionIso_scalar φ a X s))
  simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at hd
  have hn := (derivedRestrictScalarsHomologyIso φ i).inv.naturality (s • 𝟙 Y.obj)
  simp only [Functor.comp_map] at hn
  change (ModuleCat.restrictScalars φ).map
      ((DerivedCategory.homologyFunctor (ModuleCat S) i).map (s • 𝟙 Y.obj)) ≫
      ((derivedRestrictScalarsHomologyIso φ i).app Y.obj).inv =
    ((derivedRestrictScalarsHomologyIso φ i).app Y.obj).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) i).map
        ((derivedRestrictScalars φ).map (s • 𝟙 Y.obj)) at hn
  dsimp only [Y] at hn
  have ht : (ModuleCat.restrictScalars φ).map
      ((DerivedCategory.homologyFunctor (ModuleCat S) i).map (s • 𝟙 Y.obj)) ≫
      (completedBaseChangeTensorRestrictionHomologyIso φ a X i).hom =
    (completedBaseChangeTensorRestrictionHomologyIso φ a X i).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) i).map
        ((boundedAboveDerivedCompletionFunctor R a).map (boundedAboveDerivedTensor.map
          (CategoryTheory.Prod.mkHom
            (show derivedBaseChangeScalarObject φ ⟶ derivedBaseChangeScalarObject φ from
              boundedAboveDerivedSingleFunctor.map (restrictedScalarMultiplication φ s)) (𝟙 X)))).hom := by
    simp only [completedBaseChangeTensorRestrictionHomologyIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Category.assoc]
    rw [← Category.assoc, hn, Category.assoc]
    congr 1
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id] at ht
  exact congrArg (fun f => f.hom x) ht

end SerrePositivity.DerivedCompletion

module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedKoszulReduction
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModels

/-! # Principal derived completion preserves boundedness above

A uniform strict upper bound for a tower gives an upper bound one degree higher
for its actual holim model. This suffices to restrict completion to D-minus.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- A uniform upper bound on the terms of a tower bounds its product. -/
lemma complexTowerProduct_isStrictlyLE
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    (hK : ∀ n, (K n).IsStrictlyLE b) : (piObj K).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have (n : ℕ) : Subsingleton ((K n).X i) := by
    have := hK n
    exact ModuleCat.isZero_iff_subsingleton.mp ((K n).isZero_of_isStrictlyLE b i hi)
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ((complexProductDegreeEquiv R K i).injective.subsingleton)

/-- Holim raises a uniform strict upper bound by at most one degree. -/
lemma complexTowerHomotopyLimit_isStrictlyLE
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (b : ℤ) (hK : ∀ n, (K n).IsStrictlyLE b) :
    (complexTowerHomotopyLimit R K t).IsStrictlyLE (b + 1) := by
  have := complexTowerProduct_isStrictlyLE R K b hK
  have hc : (CochainComplex.mappingCone (complexTowerDifference R K t)).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨(piObj K).isZero_of_isStrictlyLE b (i + 1) (by omega),
      (piObj K).isZero_of_isStrictlyLE b i hi⟩
  exact CochainComplex.isStrictlyLE_shift _ b (-1) (b + 1) (by omega)

/-- The actual completion complex of an upper-bounded complex is upper bounded. -/
lemma complexCompletion_isStrictlyLE (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] : ((complexCompletionFunctor R a).obj K).IsStrictlyLE (b + 1) := by
  apply complexTowerHomotopyLimit_isStrictlyLE R _ _ b
  intro n
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyLE b (i + 1) (by omega), K.isZero_of_isStrictlyLE b i hi⟩

/-- Completion of an actual bounded-above derived object remains bounded above. -/
lemma derivedComplexCompletionFunctor_isBoundedAbove (a : R)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    ∃ b : ℤ, ((derivedComplexCompletionFunctor R a).obj X.obj).IsLE b := by
  let P := boundedAboveDerivedChosenModel X
  have := complexCompletion_isStrictlyLE R a P.complex P.bound
  let e : DerivedCategory.Q.obj ((complexCompletionFunctor R a).obj P.complex) ≅
      (derivedComplexCompletionFunctor R a).obj X.obj :=
    (derivedComplexCompletionComparison R a).symm.app P.complex ≪≫
      (derivedComplexCompletionFunctor R a).mapIso P.iso
  exact ⟨P.bound + 1, DerivedCategory.TStructure.t.isLE_of_iso e (P.bound + 1)⟩

/-- Restrict actual principal completion to the standard bounded-above derived category. -/
def boundedAboveDerivedCompletionFunctor (a : R) :
    DerivedCategory.Minus (ModuleCat.{u} R) ⥤ DerivedCategory.Minus (ModuleCat.{u} R) :=
  DerivedCategory.TStructure.t.minus.lift
    (DerivedCategory.Minus.ι ⋙ derivedComplexCompletionFunctor R a)
    (derivedComplexCompletionFunctor_isBoundedAbove R a)

/-- This restriction computes exactly the same completion object and morphisms. -/
def boundedAboveDerivedCompletionInclusionIso (a : R) :
    boundedAboveDerivedCompletionFunctor R a ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.Minus.ι ⋙ derivedComplexCompletionFunctor R a := Iso.refl _

/-- The actual standard completion unit inside the bounded-above derived category. -/
def boundedAboveDerivedCompletionUnit (a : R) :
    𝟭 (DerivedCategory.Minus (ModuleCat.{u} R)) ⟶ boundedAboveDerivedCompletionFunctor R a where
  app X := ObjectProperty.homMk ((derivedComplexCompletionUnit R a).app X.obj)
  naturality {X Y} f := by
    apply InducedCategory.hom_ext
    exact (derivedComplexCompletionUnit R a).naturality f.hom

end SerrePositivity.DerivedCompletion

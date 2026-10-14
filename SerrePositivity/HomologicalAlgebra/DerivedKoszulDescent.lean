module
public import SerrePositivity.HomologicalAlgebra.PowerTorsionDerivedDescent
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedKoszulReduction
public import SerrePositivity.HomologicalAlgebra.KoszulCoordinateControl

/-! # Completely faithfully flat descent on actual power-Koszul reductions -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
open DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- Every actual scalar-cone homology group is annihilated by the coordinate itself. -/
lemma derivedScalarCone_homology_annihilated (a : R)
    (X : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) :
    ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((derivedScalarConeFunctor R a).obj X), a • x = 0 := by
  let K := DerivedCategory.Q.objPreimage X
  let e := (derivedScalarConeFunctor R a).mapIso (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫
    (derivedScalarConeComparison R a).app K
  let eH := (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app ((scalarConeFunctor a).obj K)
  intro x
  apply eH.toLinearEquiv.injective
  simp only [map_smul, map_zero]
  exact scalarCone_coordinate_homology_smul_zero a K i (eH.hom x)

/-- Actual scalar cones preserve upper bounds, including when the coordinate is a zero divisor. -/
lemma derivedScalarCone_isLE (a : R) (X : DerivedCategory (ModuleCat.{u} R))
    (b : ℤ) [X.IsLE b] : ((derivedScalarConeFunctor R a).obj X).IsLE b := by
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X b
  have : CochainComplex.IsStrictlyLE ((scalarConeFunctor a).obj K) b := by
    change (CochainComplex.mappingCone (smulId a K)).IsStrictlyLE b
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨K.isZero_of_isStrictlyLE b (i + 1) (by omega),
      K.isZero_of_isStrictlyLE b i hi⟩
  let ei : (derivedScalarConeFunctor R a).obj X ≅
      DerivedCategory.Q.obj ((scalarConeFunctor a).obj K) :=
    (derivedScalarConeFunctor R a).mapIso e ≪≫ (derivedScalarConeComparison R a).app K
  exact DerivedCategory.TStructure.t.isLE_of_iso ei.symm b

/-- Actual power-Koszul reduction as a functor on the standard bounded-above derived category. -/
def boundedAboveDerivedScalarCone (a : R) :
    DerivedCategory.Minus (ModuleCat.{u} R) ⥤ DerivedCategory.Minus (ModuleCat.{u} R) :=
  DerivedCategory.TStructure.t.minus.lift
    (DerivedCategory.Minus.ι ⋙ derivedScalarConeFunctor R a) (by
      intro X
      obtain ⟨b, hb⟩ := X.property
      exact ⟨b, derivedScalarCone_isLE R a X.obj b⟩)

variable {R} {S : Type u} [CommRing S] (φ : R →+* S)

/-- Power-Koszul homology has the Tor-acyclicity needed for actual derived base change. -/
lemma derivedKoszul_homologyTorAcyclic (a : R)
    (hS : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ)) (n : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    homologyTorAcyclic φ ((boundedAboveDerivedScalarCone R (a ^ n)).obj X).obj :=
  homologyTorAcyclic_of_power_torsion φ a hS n _
    (fun i => derivedScalarCone_homology_annihilated R (a ^ n) X.obj i)

/-- Actual scalar annihilation on every power-Koszul reduction descends faithfully. -/
lemma derivedKoszulHomology_annihilated_iff (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ)) (n : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (r : R) (i : ℤ) :
    (∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
      ((boundedAboveDerivedBaseChange φ).obj
        ((boundedAboveDerivedScalarCone R (a ^ n)).obj X)).obj, φ r • x = 0) ↔
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        ((derivedScalarConeFunctor R (a ^ n)).obj X.obj), r • x = 0 :=
  powerTorsionDerivedHomology_annihilated_iff φ a hS n _
    (fun j => derivedScalarCone_homology_annihilated R (a ^ n) X.obj j) r i

/-- Faithful power-Koszul descent preserves a single exponent shared by all stages and degrees. -/
lemma derivedKoszulHomology_uniform_annihilated_iff (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (g : R) (degrees : Set ℤ) :
    (∃ N : ℕ, ∀ n : ℕ, ∀ i ∈ degrees,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj
          ((boundedAboveDerivedScalarCone R (a ^ n)).obj X)).obj, (φ g) ^ N • x = 0) ↔
      ∃ N : ℕ, ∀ n : ℕ, ∀ i ∈ degrees,
        ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
          ((derivedScalarConeFunctor R (a ^ n)).obj X.obj), g ^ N • x = 0 :=
  powerTorsionDerivedHomology_uniform_annihilated_iff φ a hS
    (fun n => (boundedAboveDerivedScalarCone R (a ^ n)).obj X)
    (fun n i => derivedScalarCone_homology_annihilated R (a ^ n) X.obj i) g degrees

end SerrePositivity

module
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor

/-! # Discrete scalar extensions and the Tor hypotheses for ordinary factors -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- All higher Tor groups with the scalar ring vanish for this module. -/
def scalarExtensionTorVanishing (M : ModuleCat.{u} R) : Prop :=
  ∀ n : ℕ, 0 < n → IsZero (((Tor (ModuleCat.{u} R) n).obj (baseChangeScalarModule φ)).obj M)

lemma derivedSingleHomology_isZero {A : Type u} [CommRing A]
    (M : ModuleCat.{u} A) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M)) :=
  (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 M i hi).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app
      ((CochainComplex.singleFunctor (ModuleCat A) 0).obj M))

/-- Invertibility of the standard augmentation is equivalent to higher Tor vanishing. -/
lemma derivedModuleBaseChangeAugmentation_isIso_iff (M : ModuleCat.{u} R) :
    IsIso ((derivedModuleBaseChangeAugmentation φ).app M) ↔ scalarExtensionTorVanishing φ M := by
  constructor
  · intro h
    have := h
    apply (derivedModuleBaseChange_negative_homology_vanishes_iff φ M).mp
    intro n hn
    exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars φ).obj M) (-(n : ℤ))
      (by omega)).of_iso ((DerivedCategory.homologyFunctor (ModuleCat S) (-(n : ℤ))).mapIso
        (asIso ((derivedModuleBaseChangeAugmentation φ).app M)))
  · intro hTor
    have hneg := (derivedModuleBaseChange_negative_homology_vanishes_iff φ M).mpr hTor
    apply (DerivedCategory.isIso_iff (ModuleCat S) _).mpr
    intro i
    by_cases hi : i = 0
    · subst i
      have hc : IsIso ((DerivedCategory.homologyFunctor (ModuleCat S) 0).map
          ((derivedModuleBaseChangeAugmentation φ).app M) ≫
          (realizedSingleH0Iso S).hom.app ((ModuleCat.extendScalars φ).obj M)) := by
        rw [derivedModuleBaseChangeAugmentation_homology]
        infer_instance
      exact IsIso.of_isIso_comp_right _
        ((realizedSingleH0Iso S).hom.app ((ModuleCat.extendScalars φ).obj M))
    · have hs : IsZero ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj
          ((derivedModuleBaseChange φ).obj M)) := by
        by_cases hpos : 0 < i
        · exact derivedModuleBaseChange_homology_isZero_positive φ M i hpos
        · let n := (-i).toNat
          have hn : 0 < n := by dsimp [n]; omega
          have he : i = -(n : ℤ) := by dsimp [n]; omega
          rw [he]
          exact hneg n hn
      exact hs.isIso (derivedSingleHomology_isZero ((ModuleCat.extendScalars φ).obj M) i hi) _

/-- Replace a derived scalar extension by its ordinary module using the standard augmentation. -/
def boundedAboveDerivedBaseChangeModuleAugmentationIso (M : ModuleCat.{u} R)
    (hTor : scalarExtensionTorVanishing φ M) :
    (boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedSingleFunctor.obj M) ≅
      boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars φ).obj M) := by
  have := (derivedModuleBaseChangeAugmentation_isIso_iff φ M).mpr hTor
  have : IsIso ((boundedAboveDerivedBaseChangeModuleAugmentation φ).app M) := by
    change IsIso ((boundedAboveDerivedBaseChangeModuleNatIso φ).hom.app M ≫
      (derivedModuleBaseChangeAugmentation φ).app M)
    infer_instance
  exact ObjectProperty.isoMk _ (asIso ((boundedAboveDerivedBaseChangeModuleAugmentation φ).app M))

/-- Replacing both derived scalar extensions requires the Tor hypothesis for each factor. -/
def boundedAboveDerivedTensorBaseChangeModuleIso (M N : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing φ M) (hN : scalarExtensionTorVanishing φ N) :
    (boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj M, boundedAboveDerivedSingleFunctor.obj N)) ≅
      boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars φ).obj M),
          boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars φ).obj N)) :=
  boundedAboveDerivedTensorBaseChangeIso φ _ _ ≪≫ boundedAboveDerivedTensor.mapIso
    (Iso.prod (boundedAboveDerivedBaseChangeModuleAugmentationIso φ M hM)
      (boundedAboveDerivedBaseChangeModuleAugmentationIso φ N hN))

lemma boundedAboveDerivedBaseChangeModuleAugmentationIso_naturality
    {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hM : scalarExtensionTorVanishing φ M) (hN : scalarExtensionTorVanishing φ N) :
    (boundedAboveDerivedBaseChange φ).map (boundedAboveDerivedSingleFunctor.map f) ≫
        (boundedAboveDerivedBaseChangeModuleAugmentationIso φ N hN).hom =
      (boundedAboveDerivedBaseChangeModuleAugmentationIso φ M hM).hom ≫
        boundedAboveDerivedSingleFunctor.map ((ModuleCat.extendScalars φ).map f) := by
  apply InducedCategory.hom_ext
  simp only [boundedAboveDerivedBaseChangeModuleAugmentationIso, ObjectProperty.isoMk,
    ObjectProperty.homMk_hom, ObjectProperty.FullSubcategory.comp_hom, asIso_hom]
  exact (boundedAboveDerivedBaseChangeModuleAugmentation φ).naturality f

/-- The ordinary comparison respects both module maps and retains both Tor hypotheses. -/
lemma boundedAboveDerivedTensorBaseChangeModuleIso_naturality
    {M M' N N' : ModuleCat.{u} R} (f : M ⟶ M') (g : N ⟶ N')
    (hM : scalarExtensionTorVanishing φ M) (hM' : scalarExtensionTorVanishing φ M')
    (hN : scalarExtensionTorVanishing φ N) (hN' : scalarExtensionTorVanishing φ N') :
    (boundedAboveDerivedBaseChange φ).map (boundedAboveDerivedTensor.map
        (boundedAboveDerivedSingleFunctor.map f, boundedAboveDerivedSingleFunctor.map g)) ≫
        (boundedAboveDerivedTensorBaseChangeModuleIso φ M' N' hM' hN').hom =
      (boundedAboveDerivedTensorBaseChangeModuleIso φ M N hM hN).hom ≫
        boundedAboveDerivedTensor.map
          (boundedAboveDerivedSingleFunctor.map ((ModuleCat.extendScalars φ).map f),
            boundedAboveDerivedSingleFunctor.map ((ModuleCat.extendScalars φ).map g)) := by
  simp only [boundedAboveDerivedTensorBaseChangeModuleIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.prod_hom]
  rw [← Category.assoc, boundedAboveDerivedTensorBaseChangeIso_naturality, Category.assoc]
  simp only [Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  apply congrArg boundedAboveDerivedTensor.map
  apply Prod.ext
  · exact boundedAboveDerivedBaseChangeModuleAugmentationIso_naturality φ f hM hM'
  · exact boundedAboveDerivedBaseChangeModuleAugmentationIso_naturality φ g hN hN'

end SerrePositivity

module
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeTensor
public import SerrePositivity.HomologicalAlgebra.DerivedTensorLinear

/-! # The original target-scalar action in the restricted base-change tensor model -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Multiplication by the actual target scalar on the original restricted scalar module. -/
def restrictedScalarMultiplication (s : S) :
    baseChangeScalarModule φ ⟶ baseChangeScalarModule φ :=
  (ModuleCat.restrictScalars φ).map (s • 𝟙 (ModuleCat.of S S))

/-- Scalars coming from the original base act by its original module structure. -/
lemma restrictedScalarMultiplication_algebraMap (r : R) :
    restrictedScalarMultiplication φ (φ r) = r • 𝟙 (baseChangeScalarModule φ) := by
  ext x
  rfl

/-- Scalar multiplication under the standard pointwise restriction–tensor comparison. -/
lemma extendRestrictTensorIso_scalar (M : ModuleCat.{u} R) (s : S) :
    (ModuleCat.restrictScalars φ).map (s • 𝟙 ((ModuleCat.extendScalars φ).obj M)) ≫
        (extendRestrictTensorIso φ).hom.app M =
      (extendRestrictTensorIso φ).hom.app M ≫ (restrictedScalarMultiplication φ s ▷ M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The original target scalar becomes multiplication on the unresolved scalar factor
of the actual tensor complex. -/
lemma restrictedBaseChangeComplexIso_scalar
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (s : S) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
        (s • 𝟙 (baseChange φ P)) ≫ (restrictedBaseChangeComplexIso φ P).hom =
      (restrictedBaseChangeComplexIso φ P).hom ≫ cochainTensorMap
        ((CochainComplex.singleFunctor (ModuleCat R) 0).map (restrictedScalarMultiplication φ s))
        (𝟙 P) := by
  let V := baseChangeScalarModule φ
  let c := (Functor.mapHomologicalComplexCompIso (extendRestrictTensorIso φ) (.up ℤ)).app P
  let a := cochainTensorSingleLeftIso V P
  let h := restrictedBaseChangeComplexIso φ P
  let m := cochainTensorMap
    ((CochainComplex.singleFunctor (ModuleCat R) 0).map (restrictedScalarMultiplication φ s)) (𝟙 P)
  let t := (NatTrans.mapHomologicalComplex
    ((tensoringLeft (ModuleCat R)).map (restrictedScalarMultiplication φ s)) (.up ℤ)).app P
  have hcomp : h.hom ≫ a.hom = c.hom := by
    change (c.hom ≫ a.inv) ≫ a.hom = c.hom
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hm : m ≫ a.hom = a.hom ≫ t :=
    cochainTensorSingleLeftIso_module_naturality (restrictedScalarMultiplication φ s) P
  have hc : ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).map
      (s • 𝟙 (baseChange φ P)) ≫ c.hom = c.hom ≫ t := by
    apply HomologicalComplex.hom_ext
    intro n
    exact extendRestrictTensorIso_scalar φ (P.X n) s
  apply (cancel_mono a.hom).mp
  change (_ ≫ h.hom) ≫ a.hom = (h.hom ≫ m) ≫ a.hom
  rw [Category.assoc, hcomp, hc, Category.assoc, hm, ← Category.assoc, hcomp]

/-- In the actual derived model the same target scalar acts on the same unresolved scalar factor. -/
lemma restrictedDerivedBaseChangeModelIso_scalar
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (s : S) :
    ((boundedAboveDerivedRestrictScalars φ).map
        (s • 𝟙 ((boundedAboveDerivedBaseChange φ).obj X))).hom ≫
        (restrictedDerivedBaseChangeModelIso φ X).hom =
      (restrictedDerivedBaseChangeModelIso φ X).hom ≫ DerivedCategory.Q.map
        (cochainTensorMap ((CochainComplex.singleFunctor (ModuleCat R) 0).map
          (restrictedScalarMultiplication φ s)) (𝟙 (boundedAboveDerivedChosenModel X).complex)) := by
  let P := boundedAboveDerivedBaseChangeModel φ X
  have hn := boundedAboveExactDerivedModelIso_naturality (ModuleCat.restrictScalars φ)
    P P (s • 𝟙 ((boundedAboveDerivedBaseChange φ).obj X)) (s • 𝟙 P.complex)
    (by
      change DerivedCategory.Q.map (s • 𝟙 P.complex) ≫ 𝟙 _ = 𝟙 _ ≫ _
      simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Category.comp_id,
        Category.id_comp]
      rfl)
  simp only [restrictedDerivedBaseChangeModelIso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]
  erw [← Category.assoc, hn, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map
    (restrictedBaseChangeComplexIso_scalar φ (boundedAboveDerivedChosenModel X).complex s)

/-- Removing the scalar-ring resolution respects every endomorphism of that scalar module. -/
lemma derivedScalarTensorModelIso_first_naturality
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (f : baseChangeScalarModule φ ⟶ baseChangeScalarModule φ) :
    (boundedAboveDerivedTensor.map
      (boundedAboveDerivedSingleFunctor.map f, 𝟙 X)).hom ≫
        (derivedScalarTensorModelIso φ X).hom =
      (derivedScalarTensorModelIso φ X).hom ≫ DerivedCategory.Q.map
        (cochainTensorMap ((CochainComplex.singleFunctor (ModuleCat R) 0).map f)
          (𝟙 (boundedAboveDerivedChosenModel X).complex)) := by
  let P := projectiveResolution (baseChangeScalarModule φ)
  let Q := boundedAboveDerivedChosenModel X
  have hp : DerivedCategory.Q.map (extLift P f P) ≫
      (derivedBaseChangeScalarModel φ).iso.hom =
        (derivedBaseChangeScalarModel φ).iso.hom ≫
          (boundedAboveDerivedSingleFunctor.map f).hom := by
    change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      projectiveResolutionCochainAugmentation_naturality]
  have hn := boundedAboveDerivedTensorModelIso_naturality
    (derivedBaseChangeScalarModel φ) (derivedBaseChangeScalarModel φ) Q Q
    (boundedAboveDerivedSingleFunctor.map f) (𝟙 X) (extLift P f P) (𝟙 Q.complex)
    hp (by simp)
  simp only [derivedScalarTensorModelIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← Category.assoc, hn, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    cochainTensorMap_comp, cochainTensorMap_comp]
  simp only [Category.id_comp, Category.comp_id]
  rw [projectiveResolutionCochainAugmentation_naturality]

/-- The original actual derived base-change/tensor comparison carries every target scalar
to multiplication on its original scalar-ring factor. -/
lemma boundedAboveDerivedBaseChangeTensorIso_scalar
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (s : S) :
    (boundedAboveDerivedRestrictScalars φ).map
        (s • 𝟙 ((boundedAboveDerivedBaseChange φ).obj X)) ≫
        (boundedAboveDerivedBaseChangeTensorIso φ X).hom =
      (boundedAboveDerivedBaseChangeTensorIso φ X).hom ≫ boundedAboveDerivedTensor.map
        (CategoryTheory.Prod.mkHom
          (show derivedBaseChangeScalarObject φ ⟶ derivedBaseChangeScalarObject φ from
            boundedAboveDerivedSingleFunctor.map (restrictedScalarMultiplication φ s)) (𝟙 X)) := by
  apply InducedCategory.hom_ext
  apply (cancel_mono (derivedScalarTensorModelIso φ X).hom).mp
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedAboveDerivedBaseChangeTensorIso,
    ObjectProperty.isoMk, ObjectProperty.homMk_hom, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [derivedScalarTensorModelIso_first_naturality φ X (restrictedScalarMultiplication φ s)]
  simp only [Iso.inv_hom_id_assoc]
  exact restrictedDerivedBaseChangeModelIso_scalar φ X s

end SerrePositivity

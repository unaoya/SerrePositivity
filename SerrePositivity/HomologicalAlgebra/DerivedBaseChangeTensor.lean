module
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModule
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import SerrePositivity.HomologicalAlgebra.RestrictedBaseChangeComplex

/-! # Restricted derived scalar extension is derived tensor with the scalar ring -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- The scalar ring as a degree-zero object over the original ring. -/
def derivedBaseChangeScalarObject : D :=
  boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule φ)

/-- A projective resolution of the scalar ring, with no flatness assumption on it. -/
def derivedBaseChangeScalarModel :
    BoundedAboveDerivedModel (derivedBaseChangeScalarObject φ).obj :=
  projectiveResolutionDerivedModel (projectiveResolution (baseChangeScalarModule φ))

/-- The scalar resolution can be removed after tensoring with a bounded-above projective model. -/
lemma scalarResolutionTensorAugmentation_quasiIso {X : DerivedCategory (ModuleCat.{u} R)}
    (P : BoundedAboveDerivedModel X) :
    QuasiIso (cochainTensorMap (projectiveResolutionCochainAugmentation
      (projectiveResolution (baseChangeScalarModule φ))) (𝟙 P.complex)) := by
  apply cochainTensor_quasiIso_left_of_boundedAboveFlat P.complex P.bound 0 0
  · exact fun i hi => P.complex.isZero_of_isStrictlyLE P.bound i hi
  · exact extRes_isZero_X (projectiveResolution (baseChangeScalarModule φ))
  · exact fun i hi =>
      CochainComplex.isZero_of_isStrictlyLE
        ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (baseChangeScalarModule φ)) 0 i hi
  · intro i
    have : Module.Projective R (P.complex.X i) := inferInstance
    infer_instance

/-- Compute the derived tensor with the scalar ring by the unresolved scalar module
and a projective representative of the other variable. -/
def derivedScalarTensorModelIso (X : D) :
    (boundedAboveDerivedTensor.obj (derivedBaseChangeScalarObject φ, X)).obj ≅
      DerivedCategory.Q.obj (cochainTensor (cochainSingleZero (baseChangeScalarModule φ))
        (boundedAboveDerivedChosenModel X).complex) := by
  have := scalarResolutionTensorAugmentation_quasiIso φ (boundedAboveDerivedChosenModel X)
  exact boundedAboveDerivedTensorModelIso _ _ (derivedBaseChangeScalarModel φ)
    (boundedAboveDerivedChosenModel X) ≪≫ asIso (DerivedCategory.Q.map
      (cochainTensorMap (projectiveResolutionCochainAugmentation
        (projectiveResolution (baseChangeScalarModule φ)))
        (𝟙 (boundedAboveDerivedChosenModel X).complex)))

/-- Compute the restricted derived scalar extension by the same tensor complex. -/
def restrictedDerivedBaseChangeModelIso (X : D) :
    ((boundedAboveDerivedRestrictScalars φ).obj ((boundedAboveDerivedBaseChange φ).obj X)).obj ≅
      DerivedCategory.Q.obj (cochainTensor (cochainSingleZero (baseChangeScalarModule φ))
        (boundedAboveDerivedChosenModel X).complex) :=
  boundedAboveDerivedRestrictScalarsModelIso φ _ (boundedAboveDerivedBaseChangeModel φ X) ≪≫
    DerivedCategory.Q.mapIso
      (restrictedBaseChangeComplexIso φ (boundedAboveDerivedChosenModel X).complex)

/-- Restricted derived scalar extension is tensor with the scalar ring over the original ring. -/
def boundedAboveDerivedBaseChangeTensorIso (X : D) :
    (boundedAboveDerivedRestrictScalars φ).obj ((boundedAboveDerivedBaseChange φ).obj X) ≅
      boundedAboveDerivedTensor.obj (derivedBaseChangeScalarObject φ, X) :=
  ObjectProperty.isoMk _ (restrictedDerivedBaseChangeModelIso φ X ≪≫
    (derivedScalarTensorModelIso φ X).symm)

lemma derivedScalarTensorModelIso_naturality {X Y : D} (f : X ⟶ Y) :
    (boundedAboveDerivedTensor.map (𝟙 (derivedBaseChangeScalarObject φ), f)).hom ≫
        (derivedScalarTensorModelIso φ Y).hom =
      (derivedScalarTensorModelIso φ X).hom ≫ DerivedCategory.Q.map (cochainTensorMap
        (𝟙 (cochainSingleZero (baseChangeScalarModule φ)))
        ((boundedAboveDerivedChosenModel X).map (boundedAboveDerivedChosenModel Y) f.hom)) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  have hn := boundedAboveDerivedTensorModelIso_naturality
    (derivedBaseChangeScalarModel φ) (derivedBaseChangeScalarModel φ) P Q
    (𝟙 (derivedBaseChangeScalarObject φ)) f (𝟙 (derivedBaseChangeScalarModel φ).complex)
    (P.map Q f.hom) (by simp) (P.map_naturality Q f.hom)
  simp only [derivedScalarTensorModelIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← Category.assoc, hn, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    cochainTensorMap_comp, cochainTensorMap_comp]
  simp only [P, Q, Category.id_comp, Category.comp_id]

lemma restrictedDerivedBaseChangeModelIso_naturality {X Y : D} (f : X ⟶ Y) :
    ((boundedAboveDerivedRestrictScalars φ).map ((boundedAboveDerivedBaseChange φ).map f)).hom ≫
        (restrictedDerivedBaseChangeModelIso φ Y).hom =
      (restrictedDerivedBaseChangeModelIso φ X).hom ≫ DerivedCategory.Q.map (cochainTensorMap
        (𝟙 (cochainSingleZero (baseChangeScalarModule φ)))
        ((boundedAboveDerivedChosenModel X).map (boundedAboveDerivedChosenModel Y) f.hom)) := by
  let a := (boundedAboveDerivedChosenModel X).map (boundedAboveDerivedChosenModel Y) f.hom
  have hn := boundedAboveExactDerivedModelIso_naturality (ModuleCat.restrictScalars φ)
    (boundedAboveDerivedBaseChangeModel φ X) (boundedAboveDerivedBaseChangeModel φ Y)
    ((boundedAboveDerivedBaseChange φ).map f)
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map a)
    (by change _ ≫ 𝟙 _ = 𝟙 _ ≫ _; simp; rfl)
  simp only [restrictedDerivedBaseChangeModelIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  erw [← Category.assoc, hn, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (restrictedBaseChangeComplexIso_naturality φ a)

lemma boundedAboveDerivedBaseChangeTensorIso_naturality {X Y : D} (f : X ⟶ Y) :
    (boundedAboveDerivedRestrictScalars φ).map ((boundedAboveDerivedBaseChange φ).map f) ≫
        (boundedAboveDerivedBaseChangeTensorIso φ Y).hom =
      (boundedAboveDerivedBaseChangeTensorIso φ X).hom ≫
        boundedAboveDerivedTensor.map (𝟙 (derivedBaseChangeScalarObject φ), f) := by
  apply InducedCategory.hom_ext
  apply (cancel_mono (derivedScalarTensorModelIso φ Y).hom).mp
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedAboveDerivedBaseChangeTensorIso,
    ObjectProperty.isoMk, ObjectProperty.homMk_hom, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [derivedScalarTensorModelIso_naturality φ f]
  simp only [Iso.inv_hom_id_assoc]
  exact restrictedDerivedBaseChangeModelIso_naturality φ f

/-- The tensor description is a natural isomorphism of functors on actual derived objects. -/
def boundedAboveDerivedBaseChangeTensorNatIso :
    boundedAboveDerivedBaseChange φ ⋙ boundedAboveDerivedRestrictScalars φ ≅
      (((Functor.const D).obj (derivedBaseChangeScalarObject φ)).prod' (𝟭 D)) ⋙
        boundedAboveDerivedTensor :=
  NatIso.ofComponents (boundedAboveDerivedBaseChangeTensorIso φ)
    (fun f => boundedAboveDerivedBaseChangeTensorIso_naturality φ f)

/-- Tensor base change, expressed entirely over the original ring after restricting the result.
The scalar-ring tensor is on the left, matching extension-of-scalars conventions. -/
def restrictedDerivedTensorBaseChangeNatIso :
    boundedAboveDerivedTensor ⋙
        ((((Functor.const D).obj (derivedBaseChangeScalarObject φ)).prod' (𝟭 D)) ⋙
          boundedAboveDerivedTensor) ≅
      ((boundedAboveDerivedBaseChange φ).prod (boundedAboveDerivedBaseChange φ)) ⋙
        boundedAboveDerivedTensor ⋙ boundedAboveDerivedRestrictScalars φ :=
  Functor.isoWhiskerLeft _ (boundedAboveDerivedBaseChangeTensorNatIso φ).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (boundedAboveDerivedTensorBaseChangeNatIso φ) _ ≪≫
    Functor.associator _ _ _

end SerrePositivity

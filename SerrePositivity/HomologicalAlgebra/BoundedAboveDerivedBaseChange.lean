module
public import SerrePositivity.HomologicalAlgebra.ProjectiveBaseChange
public import SerrePositivity.HomologicalAlgebra.BoundedAboveLeftDerived
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedAssociator
public import SerrePositivity.HomologicalAlgebra.TensorBaseChangeNaturality

/-! # Derived extension of scalars on bounded-above derived categories -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Derived extension of scalars. No flatness of the ring map is assumed. -/
def boundedAboveDerivedBaseChange :
    DerivedCategory.Minus (ModuleCat.{u} R) ⥤ DerivedCategory.Minus (ModuleCat.{u} S) :=
  boundedAboveLeftDerived (ModuleCat.extendScalars φ)

/-- Any bounded-above projective representative computes derived scalar extension. -/
def boundedAboveDerivedBaseChangeModelIso
    (X : DerivedCategory.Minus (ModuleCat.{u} R)) (P : BoundedAboveDerivedModel X.obj) :
    ((boundedAboveDerivedBaseChange φ).obj X).obj ≅
      DerivedCategory.Q.obj (baseChange φ P.complex) :=
  boundedAboveLeftDerivedModelIso (ModuleCat.extendScalars φ) X P

/-- The scalar extension of the chosen projective representative stays projective. -/
def boundedAboveDerivedBaseChangeModel (X : DerivedCategory.Minus (ModuleCat.{u} R)) :
    BoundedAboveDerivedModel (((boundedAboveDerivedBaseChange φ).obj X).obj) where
  complex := baseChange φ (boundedAboveDerivedChosenModel X).complex
  bound := (boundedAboveDerivedChosenModel X).bound
  bounded := inferInstance
  projective n := by
    have := projective_baseChange φ ((boundedAboveDerivedChosenModel X).complex.X n)
    change Projective ((ModuleCat.extendScalars φ).obj
      ((boundedAboveDerivedChosenModel X).complex.X n))
    exact ModuleCat.projective_of_categoryTheory_projective _
  iso := Iso.refl _

/-- The canonical tensor base-change comparison for actual derived objects. -/
def boundedAboveDerivedTensorBaseChangeIso
    (X Y : DerivedCategory.Minus (ModuleCat.{u} R)) :
    (boundedAboveDerivedBaseChange φ).obj (boundedAboveDerivedTensor.obj (X, Y)) ≅
      boundedAboveDerivedTensor.obj
        ((boundedAboveDerivedBaseChange φ).obj X, (boundedAboveDerivedBaseChange φ).obj Y) :=
  ObjectProperty.isoMk _
    (boundedAboveDerivedBaseChangeModelIso φ _ (boundedAboveDerivedTensorModel X Y) ≪≫
      DerivedCategory.Q.mapIso (cochainTensorBaseChangeIso φ
        (boundedAboveDerivedChosenModel X).complex (boundedAboveDerivedChosenModel Y).complex) ≪≫
      (boundedAboveDerivedTensorModelIso _ _ (boundedAboveDerivedBaseChangeModel φ X)
        (boundedAboveDerivedBaseChangeModel φ Y)).symm)

/-- Derived tensor base change is natural in both actual derived morphisms. -/
lemma boundedAboveDerivedTensorBaseChangeIso_naturality
    {X X' Y Y' : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ X') (g : Y ⟶ Y') :
    (boundedAboveDerivedBaseChange φ).map (boundedAboveDerivedTensor.map (f, g)) ≫
        (boundedAboveDerivedTensorBaseChangeIso φ X' Y').hom =
      (boundedAboveDerivedTensorBaseChangeIso φ X Y).hom ≫ boundedAboveDerivedTensor.map
        ((boundedAboveDerivedBaseChange φ).map f, (boundedAboveDerivedBaseChange φ).map g) := by
  let F := ModuleCat.extendScalars φ
  let P := boundedAboveDerivedChosenModel X
  let P' := boundedAboveDerivedChosenModel X'
  let Q := boundedAboveDerivedChosenModel Y
  let Q' := boundedAboveDerivedChosenModel Y'
  let a := P.map P' f.hom
  let b := Q.map Q' g.hom
  have hl := boundedAboveLeftDerivedModelIso_naturality F
    (boundedAboveDerivedTensorModel X Y) (boundedAboveDerivedTensorModel X' Y')
    (boundedAboveDerivedTensor.map (f, g)) (cochainTensorMap a b)
    (by change _ ≫ 𝟙 _ = 𝟙 _ ≫ _; simp; rfl)
  have hr := boundedAboveDerivedTensorModelIso_naturality
    (boundedAboveDerivedBaseChangeModel φ X) (boundedAboveDerivedBaseChangeModel φ X')
    (boundedAboveDerivedBaseChangeModel φ Y) (boundedAboveDerivedBaseChangeModel φ Y')
    ((boundedAboveDerivedBaseChange φ).map f) ((boundedAboveDerivedBaseChange φ).map g)
    ((F.mapHomologicalComplex (.up ℤ)).map a) ((F.mapHomologicalComplex (.up ℤ)).map b)
    (by change _ ≫ 𝟙 _ = 𝟙 _ ≫ _; simp; rfl)
    (by change _ ≫ 𝟙 _ = 𝟙 _ ≫ _; simp; rfl)
  apply InducedCategory.hom_ext
  apply (cancel_mono (boundedAboveDerivedTensorModelIso _ _
    (boundedAboveDerivedBaseChangeModel φ X') (boundedAboveDerivedBaseChangeModel φ Y')).hom).mp
  simp only [ObjectProperty.FullSubcategory.comp_hom, boundedAboveDerivedTensorBaseChangeIso,
    ObjectProperty.isoMk, ObjectProperty.homMk_hom, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hr]
  simp only [Iso.inv_hom_id_assoc]
  erw [← Category.assoc, hl, Category.assoc]
  congr 1
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  exact cochainTensorBaseChangeIso_naturality φ a b

/-- The tensor base-change formula is a natural isomorphism of bifunctors. -/
def boundedAboveDerivedTensorBaseChangeNatIso :
    boundedAboveDerivedTensor ⋙ boundedAboveDerivedBaseChange φ ≅
      ((boundedAboveDerivedBaseChange φ).prod (boundedAboveDerivedBaseChange φ)) ⋙
        boundedAboveDerivedTensor :=
  NatIso.ofComponents (fun X => boundedAboveDerivedTensorBaseChangeIso φ X.1 X.2)
    (fun f => boundedAboveDerivedTensorBaseChangeIso_naturality φ f.1 f.2)

end SerrePositivity

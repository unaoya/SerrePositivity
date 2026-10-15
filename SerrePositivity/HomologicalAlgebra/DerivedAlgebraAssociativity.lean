module
public import SerrePositivity.HomologicalAlgebra.CochainDiscreteAlgebra
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationModels
public import SerrePositivity.HomologicalAlgebra.DerivedDiscreteAlgebraMaps

/-! # Associativity of the actual derived algebra multiplication -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- Compute the actual derived product on any projective model with its actual augmentation. -/
lemma boundedAboveDerivedAlgebraMul_projective_model
    (A : Type u) [CommRing A] [Algebra R A]
    (P : BoundedAboveDerivedModel
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)).obj)
    (ε : P.complex ⟶ cochainSingleZero (ModuleCat.of R A))
    (hε : DerivedCategory.Q.map ε = P.iso.hom) :
    (boundedAboveDerivedAlgebraMul (R := R) A).hom =
      (boundedAboveDerivedTensorModelIso
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A))
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)) P P).hom ≫
      DerivedCategory.Q.map
        (cochainTensorMap ε ε ≫ (cochainAlgebraMonObj (R := R) A).mul) := by
  change (boundedAboveDerivedTensorModuleAugmentation (ModuleCat.of R A)).app
      (ModuleCat.of R A) ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom (LinearMap.mul' R A)) = _
  rw [boundedAboveDerivedTensorModuleAugmentation_projective_models P P ε ε hε hε]
  change (_ ≫ DerivedCategory.Q.map _) ≫ DerivedCategory.Q.map
    ((CochainComplex.singleFunctor (ModuleCat R) 0).map
      (ModuleCat.ofHom (LinearMap.mul' R A))) = _
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rfl

/-- A product lift need only agree with the canonical augmented product up to homotopy
in order to satisfy associativity after the actual derived localization. -/
lemma cochainAlgebraMul_homotopy_lift_assoc
    (A : Type u) [CommRing A] [Algebra R A]
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (ε : P ⟶ cochainSingleZero (ModuleCat.of R A))
    (f : cochainTensor P P ⟶ P)
    (h : Homotopy (f ≫ ε)
      (cochainTensorMap ε ε ≫ (cochainAlgebraMonObj (R := R) A).mul)) :
    DerivedCategory.Q.map (cochainTensorMap f (𝟙 P) ≫ cochainTensorMap ε ε ≫
        (cochainAlgebraMonObj (R := R) A).mul) =
      DerivedCategory.Q.map ((cochainTensorAssociator P P P).hom ≫
        cochainTensorMap (𝟙 P) f ≫ cochainTensorMap ε ε ≫
          (cochainAlgebraMonObj (R := R) A).mul) := by
  have hL := DerivedCategory.Q_map_eq_of_homotopy (ModuleCat R)
    (cochainTensorHomotopyLeft h ε)
  have hR := DerivedCategory.Q_map_eq_of_homotopy (ModuleCat R)
    (cochainTensorHomotopyRight ε h)
  have cL : cochainTensorMap f (𝟙 P) ≫ cochainTensorMap ε ε =
      cochainTensorMap (f ≫ ε) ε := by
    rw [cochainTensorMap_comp, Category.id_comp]
  have cR : cochainTensorMap (𝟙 P) f ≫ cochainTensorMap ε ε =
      cochainTensorMap ε (f ≫ ε) := by
    rw [cochainTensorMap_comp, Category.id_comp]
  rw [← Category.assoc (cochainTensorMap f (𝟙 P)), cL,
    ← Category.assoc (cochainTensorMap (𝟙 P) f), cR]
  simp only [CategoryTheory.Functor.map_comp]
  rw [hL, hR]
  simp only [← CategoryTheory.Functor.map_comp]
  exact congrArg DerivedCategory.Q.map (cochainAlgebraMul_augmented_assoc A P ε)

/-- The canonical derived algebra product is associative for the actual derived associator. -/
lemma boundedAboveDerivedAlgebraMul_assoc (A : Type u) [CommRing A] [Algebra R A] :
    let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)
    let m := boundedAboveDerivedAlgebraMul (R := R) A
    boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom m (𝟙 X)) ≫ m =
      (boundedAboveDerivedTensorAssociator X X X).hom ≫
        boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom (𝟙 X) m) ≫ m := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R A)
  let m := boundedAboveDerivedAlgebraMul (R := R) A
  let P := projectiveResolutionDerivedModel (projectiveResolution (ModuleCat.of R A))
  let ε := projectiveResolutionCochainAugmentation (projectiveResolution (ModuleCat.of R A))
  let μ := (cochainAlgebraMonObj (R := R) A).mul
  let PP := boundedAboveTensorModelOf X X P P
  let L := boundedAboveTensorModelOf (boundedAboveDerivedTensor.obj (X, X)) X PP P
  let RR := boundedAboveTensorModelOf X (boundedAboveDerivedTensor.obj (X, X)) P PP
  let f := PP.map P m.hom
  let aL := boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom m (𝟙 X))
  let aR := boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom (𝟙 X) m)
  let aα := (boundedAboveDerivedTensorAssociator X X X).hom
  have hf : DerivedCategory.Q.map f ≫ P.iso.hom = PP.iso.hom ≫ m.hom :=
    PP.map_naturality P m.hom
  have hprod : DerivedCategory.Q.map (cochainTensorMap ε ε ≫ μ) =
      PP.iso.hom ≫ m.hom := by
    change _ = (boundedAboveDerivedTensorModelIso X X P P).inv ≫
      (boundedAboveDerivedAlgebraMul (R := R) A).hom
    rw [boundedAboveDerivedAlgebraMul_projective_model A P ε rfl]
    erw [Iso.inv_hom_id_assoc]
  have h : Homotopy (f ≫ ε) (cochainTensorMap ε ε ≫ μ) := by
    apply homotopyOfDerivedMapEq
    rw [CategoryTheory.Functor.map_comp]
    change DerivedCategory.Q.map f ≫ P.iso.hom = _
    exact hf.trans hprod.symm
  have hL := boundedAboveTensorModelOf_map
    (X := boundedAboveDerivedTensor.obj (X, X)) (X' := X) (Y := X) (Y' := X)
    PP P P P m (𝟙 X) f (𝟙 P.complex) hf (by simp)
  have hR := boundedAboveTensorModelOf_map
    (X := X) (X' := X) (Y := boundedAboveDerivedTensor.obj (X, X)) (Y' := X)
    P P PP P (𝟙 X) m (𝟙 P.complex) f (by simp) hf
  have hα := boundedAboveAssociatorModel_map X X X P P P
  change DerivedCategory.Q.map (cochainTensorMap f (𝟙 P.complex)) ≫ PP.iso.hom =
    L.iso.hom ≫ aL.hom at hL
  change DerivedCategory.Q.map (cochainTensorMap (𝟙 P.complex) f) ≫ PP.iso.hom =
    RR.iso.hom ≫ aR.hom at hR
  change DerivedCategory.Q.map (cochainTensorAssociator P.complex P.complex P.complex).hom ≫
      RR.iso.hom = L.iso.hom ≫ aα.hom at hα
  have eL : L.iso.hom ≫ aL.hom ≫ m.hom =
      DerivedCategory.Q.map
        (cochainTensorMap f (𝟙 P.complex) ≫ cochainTensorMap ε ε ≫ μ) := by
    rw [← Category.assoc, ← hL, Category.assoc, ← hprod,
      ← CategoryTheory.Functor.map_comp]
  have eR : L.iso.hom ≫ aα.hom ≫ aR.hom ≫ m.hom =
      DerivedCategory.Q.map ((cochainTensorAssociator P.complex P.complex P.complex).hom ≫
        cochainTensorMap (𝟙 P.complex) f ≫ cochainTensorMap ε ε ≫ μ) := by
    rw [← Category.assoc L.iso.hom, ← hα]
    simp only [Category.assoc]
    rw [← Category.assoc RR.iso.hom, ← hR]
    simp only [Category.assoc]
    rw [← hprod]
    simp only [← CategoryTheory.Functor.map_comp]
  change aL ≫ m = aα ≫ aR ≫ m
  apply InducedCategory.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  apply (cancel_epi L.iso.hom).mp
  rw [eL, eR]
  exact cochainAlgebraMul_homotopy_lift_assoc A P.complex ε f h

end SerrePositivity

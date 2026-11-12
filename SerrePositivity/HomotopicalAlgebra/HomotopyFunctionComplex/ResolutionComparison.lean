module

public import SerrePositivity.HomotopicalAlgebra.Generated.CommonCofibrantReplacement
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHomNaturality

/-! # A natural common comparison of cosimplicial resolution families

The pullback of the two augmentations is replaced cofibrantly using the
constructed functorial Reedy factorization. Both comparison maps are natural
trivial fibrations. Applying the actual Hom bifunctor gives a natural zigzag.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.ResolutionComparison
open ModelReplacement.CommonCofibrant
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := simplexModelCategory C

def diagramCofFactorization
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    MorphismProperty.FunctorialFactorizationData (cofibrations (SimplexCategory ⥤ C))
      (trivialFibrations (SimplexCategory ⥤ C)) := by
  let d := FunctorFactorizationSequence.functorialFactorizationData simplex
    (fun _ _ h ↦ SimplexCategory.ext h) (fun n ↦ ⟨SimplexCategory.mk n, rfl⟩) cof
  exact
    { Z := d.Z
      i := d.i
      p := d.p
      fac := d.fac
      hi := d.hi
      hp f := (reedyRight_trivialFibrations_iff simplex _).mp (d.hp f) }

lemma augmentation_trivialFibration (q : CofibrantResolutionFamily (C := C) simplex) (X : C) :
    trivialFibrations (SimplexCategory ⥤ C) (q.augmentation.app X) :=
  (reedyRight_trivialFibrations_iff simplex _).mp (q.trivial X)

variable
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (q q' : CofibrantResolutionFamily (C := C) simplex)

def common : CofibrantResolutionFamily (C := C) simplex where
  obj := ModelReplacement.CommonCofibrant.obj
    (diagramCofFactorization cof) q.augmentation q'.augmentation
  augmentation := ModelReplacement.CommonCofibrant.left
    (diagramCofFactorization cof) q.augmentation q'.augmentation ≫ q.augmentation
  cofibrant X := by
    have := ModelReplacement.CommonCofibrant.isCofibrant_obj
      (diagramCofFactorization cof) q.augmentation q'.augmentation X
    exact mem_cofibrations (initial.to ((ModelReplacement.CommonCofibrant.obj
      (diagramCofFactorization cof) q.augmentation q'.augmentation).obj X))
  trivial X := by
    have h := (trivialFibrations (SimplexCategory ⥤ C)).comp_mem _ _
      (ModelReplacement.CommonCofibrant.left_trivialFibration
        (diagramCofFactorization cof) q.augmentation q'.augmentation
        (augmentation_trivialFibration q') X) (augmentation_trivialFibration q X)
    exact (reedyRight_trivialFibrations_iff simplex _).mpr h

abbrev left : (common cof q q').obj ⟶ q.obj :=
  ModelReplacement.CommonCofibrant.left (diagramCofFactorization cof) q.augmentation q'.augmentation

abbrev right : (common cof q q').obj ⟶ q'.obj :=
  ModelReplacement.CommonCofibrant.right
    (diagramCofFactorization cof) q.augmentation q'.augmentation

lemma left_over : left cof q q' ≫ q.augmentation = (common cof q q').augmentation := rfl

lemma right_over : right cof q q' ≫ q'.augmentation = (common cof q q').augmentation :=
  (ModelReplacement.CommonCofibrant.over
    (diagramCofFactorization cof) q.augmentation q'.augmentation).symm

lemma left_weakEquivalence (X : C) (n : SimplexCategory) :
    weakEquivalences C (((left cof q q').app X).app n) :=
  (ModelReplacement.CommonCofibrant.left_trivialFibration
    (diagramCofFactorization cof) q.augmentation q'.augmentation
    (augmentation_trivialFibration q') X).2 n

lemma right_weakEquivalence (X : C) (n : SimplexCategory) :
    weakEquivalences C (((right cof q q').app X).app n) :=
  (ModelReplacement.CommonCofibrant.right_trivialFibration
    (diagramCofFactorization cof) q.augmentation q'.augmentation
    (augmentation_trivialFibration q) X).2 n

abbrev homLeft (R : C ⥤ C) : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom q.obj R ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom (common cof q q').obj R :=
  resolutionHomMapSource (left cof q q') R

abbrev homRight (R : C ⥤ C) : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom q'.obj R ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom (common cof q q').obj R :=
  resolutionHomMapSource (right cof q q') R

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma homLeft_weakEquivalence (R : C ⥤ C) (hR : ∀ Y, IsFibrant (R.obj Y))
    (X : Cᵒᵖ) (Y : C) :
    weakEquivalences SSet.{v} (((homLeft cof q q' R).app X).app Y) := by
  have := hR Y
  exact cosimplicialHomMap_weakEquivalence hcof ((left cof q q').app X.unop)
    ((common cof q q').cofibrant X.unop) (q.cofibrant X.unop)
    (left_weakEquivalence cof q q' X.unop) _

include hcof in
lemma homRight_weakEquivalence (R : C ⥤ C) (hR : ∀ Y, IsFibrant (R.obj Y))
    (X : Cᵒᵖ) (Y : C) :
    weakEquivalences SSet.{v} (((homRight cof q q' R).app X).app Y) := by
  have := hR Y
  exact cosimplicialHomMap_weakEquivalence hcof ((right cof q q').app X.unop)
    ((common cof q q').cofibrant X.unop) (q'.cofibrant X.unop)
    (right_weakEquivalence cof q q' X.unop) _

end SerrePositivity.HomotopyFunctionComplex.ResolutionComparison

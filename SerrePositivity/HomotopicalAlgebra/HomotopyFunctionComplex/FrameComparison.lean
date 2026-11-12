module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.CosimplicialFrameFamily
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionComparison

/-! # Natural comparison of a resolution with a weakly augmented frame

Only the resolution augmentation is a Reedy trivial fibration. Its
pullback gives one trivial projection; the other is a weak equivalence
by the augmentation square and two out of three.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.FrameComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]
local instance : ModelCategory (SimplexCategory ⥤ C) := simplexModelCategory C
variable
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (q : CofibrantResolutionFamily (C := C) simplex) (p : CosimplicialFrameFamily (C := C))

abbrev commonObj := ModelReplacement.CommonCofibrant.obj
  (ResolutionComparison.diagramCofFactorization cof) q.augmentation p.augmentation

abbrev left : commonObj cof q p ⟶ q.obj := ModelReplacement.CommonCofibrant.left
  (ResolutionComparison.diagramCofFactorization cof) q.augmentation p.augmentation

abbrev right : commonObj cof q p ⟶ p.obj := ModelReplacement.CommonCofibrant.right
  (ResolutionComparison.diagramCofFactorization cof) q.augmentation p.augmentation

lemma over : left cof q p ≫ q.augmentation = right cof q p ≫ p.augmentation :=
  ModelReplacement.CommonCofibrant.over
    (ResolutionComparison.diagramCofFactorization cof) q.augmentation p.augmentation

lemma commonObj_cofibrant (X : C) :
    reedyLeft simplex (cofibrations C) (initial.to ((commonObj cof q p).obj X)) := by
  have := ModelReplacement.CommonCofibrant.isCofibrant_obj
    (ResolutionComparison.diagramCofFactorization cof) q.augmentation p.augmentation X
  exact mem_cofibrations (initial.to ((commonObj cof q p).obj X))

lemma right_weakEquivalence (X : C) (n : SimplexCategory) :
    weakEquivalences C (((right cof q p).app X).app n) :=
  (ModelReplacement.CommonCofibrant.right_trivialFibration
    (ResolutionComparison.diagramCofFactorization cof) q.augmentation p.augmentation
    (ResolutionComparison.augmentation_trivialFibration q) X).2 n

lemma left_weakEquivalence (X : C) (n : SimplexCategory) :
    weakEquivalences C (((left cof q p).app X).app n) := by
  have h := congr_app (congr_app (over cof q p) X) n
  change ((left cof q p).app X).app n ≫ (q.augmentation.app X).app n =
    ((right cof q p).app X).app n ≫ (p.augmentation.app X).app n at h
  exact (weakEquivalences C).of_postcomp _ _ ((q.atObject X).augmentation_weakEquivalence n)
    (h.symm ▸ (weakEquivalences C).comp_mem _ _ (right_weakEquivalence cof q p X n) (p.weak X n))

def common : CosimplicialFrameFamily (C := C) where
  obj := commonObj cof q p
  augmentation := right cof q p ≫ p.augmentation
  cofibrant := commonObj_cofibrant cof q p
  weak X n := (weakEquivalences C).comp_mem _ _ (right_weakEquivalence cof q p X n) (p.weak X n)

abbrev homLeft (R : C ⥤ C) : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom q.obj R ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom (commonObj cof q p) R :=
  resolutionHomMapSource (left cof q p) R

abbrev homRight (R : C ⥤ C) : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom p.obj R ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom (commonObj cof q p) R :=
  resolutionHomMapSource (right cof q p) R

lemma commonHom_kanComplex (R : C ⥤ C) (hR : ∀ Y, IsFibrant (R.obj Y)) (X : Cᵒᵖ) (Y : C) :
    SSet.KanComplex (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom (commonObj cof q p) R).obj X).obj Y) := by
  have := hR Y
  exact cosimplicialHom_kanComplex _ (commonObj_cofibrant cof q p X.unop)
    ((common cof q p).homotopicallyConstant X.unop) _

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma homLeft_weakEquivalence (R : C ⥤ C) (hR : ∀ Y, IsFibrant (R.obj Y))
    (X : Cᵒᵖ) (Y : C) :
    weakEquivalences SSet.{v} (((homLeft cof q p R).app X).app Y) := by
  have := hR Y
  exact cosimplicialHomMap_weakEquivalence hcof ((left cof q p).app X.unop)
    (commonObj_cofibrant cof q p X.unop) (q.cofibrant X.unop)
    (left_weakEquivalence cof q p X.unop) _

include hcof in
lemma homRight_weakEquivalence (R : C ⥤ C) (hR : ∀ Y, IsFibrant (R.obj Y))
    (X : Cᵒᵖ) (Y : C) :
    weakEquivalences SSet.{v} (((homRight cof q p R).app X).app Y) := by
  have := hR Y
  exact cosimplicialHomMap_weakEquivalence hcof ((right cof q p).app X.unop)
    (commonObj_cofibrant cof q p X.unop) (p.cofibrant X.unop)
    (right_weakEquivalence cof q p X.unop) _

end SerrePositivity.HomotopyFunctionComplex.FrameComparison

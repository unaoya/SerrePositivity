module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.NonsingularPresentation
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Tensors of finite nonsingular simplicial sets and arbitrary maps

The construction uses only finite colimits in C. Functoriality uses the
representing Hom equivalence, so a map need not preserve nondegeneracy or
be an inclusion in a fixed ambient standard simplex.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.FiniteTensor
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C] (A : SimplexCategory ⥤ C)

abbrev obj (X : SSet.{v}) [X.Nonsingular] [X.Finite] :=
  colimit (NonsingularPresentation.diagram X ⋙ A)

abbrev homEquiv (X : SSet.{v}) [X.Nonsingular] [X.Finite] (Y : C) :
    (X ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) ≃ (obj A X ⟶ Y) :=
  NonsingularPresentation.homEquiv X A Y

abbrev unit (X : SSet.{v}) [X.Nonsingular] [X.Finite] :
    X ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj (obj A X) := (homEquiv A X (obj A X)).symm (𝟙 _)

lemma homEquiv_naturality (X : SSet.{v}) [X.Nonsingular] [X.Finite] {Y Z : C}
    (f : X ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) (p : Y ⟶ Z) :
    homEquiv A X Z (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) = homEquiv A X Y f ≫ p :=
  HomPresentation.homEquiv_naturality (NonsingularPresentation.diagram X)
    (NonsingularPresentation.cocone X) (NonsingularPresentation.isColimit X) A f p

lemma unit_comp (X : SSet.{v}) [X.Nonsingular] [X.Finite] {Y : C} (f : obj A X ⟶ Y) :
    unit A X ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f = (homEquiv A X Y).symm f := by
  apply (homEquiv A X Y).injective
  exact (homEquiv_naturality A X (unit A X) f).trans
    ((congrArg (fun g ↦ g ≫ f) ((homEquiv A X (obj A X)).apply_symm_apply (𝟙 _))).trans
      ((Category.id_comp f).trans ((homEquiv A X Y).apply_symm_apply f).symm))

variable {X Y Z : SSet.{v}} [X.Nonsingular] [X.Finite] [Y.Nonsingular] [Y.Finite]
  [Z.Nonsingular] [Z.Finite]

def map (h : X ⟶ Y) : obj A X ⟶ obj A Y := homEquiv A X (obj A Y) (h ≫ unit A Y)

lemma map_comp_homEquiv (h : X ⟶ Y) {W : C} (f : obj A Y ⟶ W) :
    map A h ≫ f = homEquiv A X W (h ≫ (homEquiv A Y W).symm f) :=
  (homEquiv_naturality A X (h ≫ unit A Y) f).symm.trans
    (congrArg (homEquiv A X W) ((Category.assoc _ _ _).trans
      (congrArg (fun g ↦ h ≫ g) (unit_comp A Y f))))

lemma map_comp_homEquiv_apply (h : X ⟶ Y) {W : C} (f : Y ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj W) :
    map A h ≫ homEquiv A Y W f = homEquiv A X W (h ≫ f) :=
  (map_comp_homEquiv A h _).trans (congrArg (homEquiv A X W)
    (congrArg (fun g ↦ h ≫ g) ((homEquiv A Y W).symm_apply_apply f)))

@[simp]
lemma map_id (X : SSet.{v}) [X.Nonsingular] [X.Finite] : map A (𝟙 X) = 𝟙 _ :=
  (congrArg (homEquiv A X (obj A X)) (Category.id_comp (unit A X))).trans
    ((homEquiv A X (obj A X)).apply_symm_apply _)

@[reassoc]
lemma map_comp (h : X ⟶ Y) (k : Y ⟶ Z) : map A h ≫ map A k = map A (h ≫ k) := by
  rw [map_comp_homEquiv]
  change homEquiv A X (obj A Z)
      (h ≫ (homEquiv A Y (obj A Z)).symm (homEquiv A Y (obj A Z) (k ≫ unit A Z))) = _
  rw [Equiv.symm_apply_apply]
  exact congrArg (homEquiv A X (obj A Z)) (Category.assoc _ _ _).symm

lemma homEquiv_symm_map_comp (h : X ⟶ Y) {W : C} (f : obj A Y ⟶ W) :
    (homEquiv A X W).symm (map A h ≫ f) = h ≫ (homEquiv A Y W).symm f :=
  (congrArg (homEquiv A X W).symm (map_comp_homEquiv A h f)).trans
    ((homEquiv A X W).symm_apply_apply _)

def iso (e : X ≅ Y) : obj A X ≅ obj A Y where
  hom := map A e.hom
  inv := map A e.inv
  hom_inv_id := (map_comp A e.hom e.inv).trans
    ((congrArg (map A) e.hom_inv_id).trans (map_id A X))
  inv_hom_id := (map_comp A e.inv e.hom).trans
    ((congrArg (map A) e.inv_hom_id).trans (map_id A Y))

abbrev objects : ObjectProperty SSet.{v} := fun X ↦ X.Finite ∧ X.Nonsingular
abbrev FiniteNonsingular := objects.{v}.FullSubcategory

instance (X : FiniteNonsingular.{v}) : X.obj.Finite := X.property.1
instance (X : FiniteNonsingular.{v}) : X.obj.Nonsingular := X.property.2

def functor : FiniteNonsingular.{v} ⥤ C where
  obj X := obj A X.obj
  map h := map A h.hom
  map_id X := map_id A X.obj
  map_comp h k := (map_comp A h.hom k.hom).symm

end SerrePositivity.HomotopyFunctionComplex.FiniteTensor

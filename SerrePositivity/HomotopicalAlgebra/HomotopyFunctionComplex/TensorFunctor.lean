module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SubcomplexTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensor

/-! # Functoriality of finite subcomplex tensors

The map on an inclusion is constructed from the proved representing
equivalence, and its action on every map out of the tensor is determined.
No diagram-level choices of maps on nondegenerate simplices are needed.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor
variable {n : SimplexCategory} {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  (A : SimplexCategory ⥤ C) {S T U : (SSet.stdSimplex.{v}.obj n).Subcomplex}

abbrev unit (S : (SSet.stdSimplex.{v}.obj n).Subcomplex) :
    S.toSSet ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj (obj S A) :=
  FiniteTensor.unit A S.toSSet

lemma homEquiv_naturality (S : (SSet.stdSimplex.{v}.obj n).Subcomplex) {Y Z : C}
    (f : S.toSSet ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) (p : Y ⟶ Z) :
    homEquiv S A Z (f ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) = homEquiv S A Y f ≫ p :=
  FiniteTensor.homEquiv_naturality A S.toSSet f p

lemma unit_comp (S : (SSet.stdSimplex.{v}.obj n).Subcomplex) {Y : C} (f : obj S A ⟶ Y) :
    unit A S ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f = (homEquiv S A Y).symm f :=
  FiniteTensor.unit_comp A S.toSSet f

def map (h : S ≤ T) : obj S A ⟶ obj T A :=
  FiniteTensor.map A (SSet.Subcomplex.homOfLE h)

lemma map_comp_homEquiv (h : S ≤ T) {Y : C} (f : obj T A ⟶ Y) :
    map A h ≫ f = homEquiv S A Y
      (SSet.Subcomplex.homOfLE h ≫ (homEquiv T A Y).symm f) :=
  FiniteTensor.map_comp_homEquiv A (SSet.Subcomplex.homOfLE h) f

lemma map_comp_homEquiv_apply (h : S ≤ T) {Y : C}
    (f : T.toSSet ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) :
    map A h ≫ homEquiv T A Y f = homEquiv S A Y (SSet.Subcomplex.homOfLE h ≫ f) :=
  FiniteTensor.map_comp_homEquiv_apply A (SSet.Subcomplex.homOfLE h) f

@[simp]
lemma map_id (S : (SSet.stdSimplex.{v}.obj n).Subcomplex) : map A (le_refl S) = 𝟙 _ :=
  FiniteTensor.map_id A S.toSSet

@[reassoc]
lemma map_comp (h : S ≤ T) (k : T ≤ U) : map A h ≫ map A k = map A (h.trans k) :=
  FiniteTensor.map_comp A (SSet.Subcomplex.homOfLE h) (SSet.Subcomplex.homOfLE k)

def functor : (SSet.stdSimplex.{v}.obj n).Subcomplex ⥤ C where
  obj S := obj S A
  map h := map A (leOfHom h)
  map_id S := map_id A S
  map_comp h k := (map_comp A (leOfHom h) (leOfHom k)).symm

lemma homEquiv_symm_map_comp (h : S ≤ T) {Y : C} (f : obj T A ⟶ Y) :
    (homEquiv S A Y).symm (map A h ≫ f) =
      SSet.Subcomplex.homOfLE h ≫ (homEquiv T A Y).symm f :=
  FiniteTensor.homEquiv_symm_map_comp A (SSet.Subcomplex.homOfLE h) f

lemma homEquiv_simplex (S : (SSet.stdSimplex.{v}.obj n).Subcomplex) {Y : C}
    (f : A.obj n ⟶ Y) :
    homEquiv S A Y (S.ι ≫ (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).symm f) =
      inclusion S A ≫ f := by
  have h := HomPresentation.homEquiv_presentationMap (diagram S)
    (NonsingularPresentation.cocone S.toSSet) (NonsingularPresentation.isColimit S.toSSet)
    A (simplexCocone S) f
  rwa [presentationMap_eq] at h

@[reassoc]
lemma map_inclusion (h : S ≤ T) : map A h ≫ inclusion T A = inclusion S A := by
  have hT : (homEquiv T A (A.obj n)).symm (inclusion T A) =
      T.ι ≫ (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj (A.obj n))).symm (𝟙 _) :=
    (homEquiv T A (A.obj n)).symm_apply_eq.mpr
      ((homEquiv_simplex A T (𝟙 _)).trans (Category.comp_id _)).symm
  rw [map_comp_homEquiv, hT, ← Category.assoc, SSet.Subcomplex.homOfLE_ι,
    homEquiv_simplex]
  exact Category.comp_id (inclusion S A)

end SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor

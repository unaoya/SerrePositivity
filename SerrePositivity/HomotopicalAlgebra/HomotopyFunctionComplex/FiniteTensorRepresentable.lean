module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensor
public import Mathlib.CategoryTheory.HomCongr

/-! # Finite tensors extend the original cosimplicial diagram

A finite nonsingular object represented by a standard simplex has tensor
isomorphic to the corresponding value of A. On the standard-simplex
diagram these comparisons are natural in all simplex morphisms.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.FiniteTensor
variable {k : SimplexCategory} {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  (A : SimplexCategory ⥤ C) (X : SSet.{v}) [X.Nonsingular] [X.Finite]
  (e : SSet.stdSimplex.{v}.obj k ≅ X)

def representationMap : obj A X ⟶ A.obj k :=
  homEquiv A X (A.obj k)
    (e.inv ≫ (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj (A.obj k))).symm (𝟙 _))

lemma representationMap_comp {Y : C} (f : A.obj k ⟶ Y) :
    representationMap A X e ≫ f = homEquiv A X Y
      (e.inv ≫ (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).symm f) := by
  have h : (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj (A.obj k))).symm (𝟙 _) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f =
        (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).symm f :=
    (SSet.yonedaEquiv_symm_comp (𝟙 (A.obj k)) ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f)).trans
      (congrArg (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).symm
        (Category.id_comp f))
  exact (homEquiv_naturality A X _ f).symm.trans
    (congrArg (homEquiv A X Y) ((Category.assoc _ _ _).trans
      (congrArg (fun g ↦ e.inv ≫ g) h)))

instance representationMap_isIso : IsIso (representationMap A X e) := by
  apply isIso_of_coyoneda_map_bijective
  intro Y
  let E : (A.obj k ⟶ Y) ≃ (obj A X ⟶ Y) :=
    (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).symm.trans
      ((Iso.homCongr e (Iso.refl _)).trans (homEquiv A X Y))
  have he : (fun f : A.obj k ⟶ Y ↦ representationMap A X e ≫ f) = E := by
    funext f
    simpa only [E, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id] using
      representationMap_comp A X e f
  exact he.symm ▸ E.bijective

abbrev representationIso : obj A X ≅ A.obj k := asIso (representationMap A X e)

def standardDiagram : SimplexCategory ⥤ FiniteNonsingular.{v} where
  obj n := ⟨SSet.stdSimplex.obj n, inferInstance, inferInstance⟩
  map f := ObjectProperty.homMk (SSet.stdSimplex.map f)
  map_id n := by
    apply ObjectProperty.hom_ext
    exact SSet.stdSimplex.map_id n
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact SSet.stdSimplex.map_comp f g

lemma standard_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    map A (SSet.stdSimplex.{v}.map f) ≫
        representationMap A (SSet.stdSimplex.obj m) (Iso.refl _) =
      representationMap A (SSet.stdSimplex.obj n) (Iso.refl _) ≫ A.map f := by
  have hL := map_comp_homEquiv_apply A (SSet.stdSimplex.{v}.map f)
    (𝟙 (SSet.stdSimplex.obj m) ≫
      (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj (A.obj m))).symm (𝟙 (A.obj m)))
  have hR := representationMap_comp A (SSet.stdSimplex.{v}.obj n) (Iso.refl _) (A.map f)
  have h : SSet.stdSimplex.{v}.map f ≫
      (𝟙 (SSet.stdSimplex.obj m) ≫
        (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj (A.obj m))).symm (𝟙 (A.obj m))) =
      𝟙 (SSet.stdSimplex.obj n) ≫
        (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj (A.obj m))).symm (A.map f) := by
    rw [Category.id_comp, Category.id_comp]
    exact (SSet.yonedaEquiv_symm_naturality_left f (𝟙 (A.obj m))).trans
      (congrArg (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj (A.obj m))).symm
        (Category.comp_id (A.map f)))
  exact hL.trans ((congrArg (homEquiv A (SSet.stdSimplex.obj n) (A.obj m)) h).trans hR.symm)

def standardIso : standardDiagram.{v} ⋙ functor A ≅ A :=
  NatIso.ofComponents (fun n ↦ representationIso A (SSet.stdSimplex.obj n) (Iso.refl _))
    (by intro n m f; exact standard_naturality A f)

end SerrePositivity.HomotopyFunctionComplex.FiniteTensor

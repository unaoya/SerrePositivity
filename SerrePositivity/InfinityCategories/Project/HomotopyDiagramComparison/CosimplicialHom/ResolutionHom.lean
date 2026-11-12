module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Opposites

/-!
分割で生成：docstring を書き直すこと
 # The simplicial Hom bifunctor of a cosimplicial resolution

Its n-simplices are the actual maps from the n-th cosimplicial object.
This module constructs strict functoriality in the resolution and target;
it does not assert derived invariance or the Kan property.
-/

@[expose] public section
universe v u
open CategoryTheory

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable {C : Type u} [Category.{v} C]

abbrev cosimplicialHom (A : SimplexCategory ⥤ C) : C ⥤ SSet.{v} :=
  yoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (Type v)).obj A.op

def cosimplicialHomMap {A B : SimplexCategory ⥤ C} (α : A ⟶ B) :
    cosimplicialHom B ⟶ cosimplicialHom A where
  app Y := Functor.whiskerRight (NatTrans.op α) (yoneda.obj Y)
  naturality X Y f := by
    ext n h
    change α.app n.unop ≫ (h ≫ f) = (α.app n.unop ≫ h) ≫ f
    exact (Category.assoc _ _ _).symm

def cosimplicialHomBifunctor : (SimplexCategory ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{v} where
  obj A := cosimplicialHom A.unop
  map α := cosimplicialHomMap α.unop
  map_id A := by
    ext Y n h
    change 𝟙 (A.unop.obj n.unop) ≫ h = h
    exact Category.id_comp h
  map_comp α β := by
    ext Y n h
    change (β.unop.app n.unop ≫ α.unop.app n.unop) ≫ h =
      β.unop.app n.unop ≫ (α.unop.app n.unop ≫ h)
    exact Category.assoc _ _ _

/-- Actual simplicial Hom after a chosen cosimplicial family and target replacement. -/
abbrev resolutionHom (Q : C ⥤ (SimplexCategory ⥤ C)) (R : C ⥤ C) :
    Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  Q.op ⋙ cosimplicialHomBifunctor ⋙ (Functor.whiskeringLeft C C SSet.{v}).obj R

@[simp]
lemma cosimplicialHom_obj (A : SimplexCategory ⥤ C) (Y : C) (n : SimplexCategoryᵒᵖ) :
    ((cosimplicialHom A).obj Y).obj n = (A.obj n.unop ⟶ Y) := rfl

@[simp]
lemma resolutionHom_obj (Q : C ⥤ (SimplexCategory ⥤ C)) (R : C ⥤ C)
    (X : Cᵒᵖ) (Y : C) (n : SimplexCategoryᵒᵖ) :
    (((resolutionHom Q R).obj X).obj Y).obj n = ((Q.obj X.unop).obj n.unop ⟶ R.obj Y) := rfl

@[simp]
lemma resolutionHom_map_source (Q : C ⥤ (SimplexCategory ⥤ C)) (R : C ⥤ C)
    {X X' : Cᵒᵖ} (f : X ⟶ X') (Y : C) (n : SimplexCategoryᵒᵖ)
    (h : (Q.obj X.unop).obj n.unop ⟶ R.obj Y) :
    ((((resolutionHom Q R).map f).app Y).app n) h = (Q.map f.unop).app n.unop ≫ h := rfl

@[simp]
lemma resolutionHom_map_target (Q : C ⥤ (SimplexCategory ⥤ C)) (R : C ⥤ C)
    (X : Cᵒᵖ) {Y Y' : C} (f : Y ⟶ Y') (n : SimplexCategoryᵒᵖ)
    (h : (Q.obj X.unop).obj n.unop ⟶ R.obj Y) :
    ((((resolutionHom Q R).obj X).map f).app n) h = h ≫ R.map f := rfl

@[simp]
lemma resolutionHom_map_simplex (Q : C ⥤ (SimplexCategory ⥤ C)) (R : C ⥤ C)
    (X : Cᵒᵖ) (Y : C) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (h : (Q.obj X.unop).obj n.unop ⟶ R.obj Y) :
    ((((resolutionHom Q R).obj X).obj Y).map θ) h = (Q.obj X.unop).map θ.unop ≫ h := rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom

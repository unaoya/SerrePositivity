module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.ResolutionHom

/-! # Natural changes of the resolution family in the actual Hom bifunctor -/

@[expose] public section
universe v u
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C]

def resolutionHomMapSource {Q Q' : C ⥤ (SimplexCategory ⥤ C)} (α : Q ⟶ Q') (R : C ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q' R ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q R :=
  Functor.whiskerRight (NatTrans.op α)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ (Functor.whiskeringLeft C C SSet.{v}).obj R)

@[simp]
lemma resolutionHomMapSource_app {Q Q' : C ⥤ (SimplexCategory ⥤ C)} (α : Q ⟶ Q') (R : C ⥤ C)
    (X : Cᵒᵖ) (Y : C) :
    ((resolutionHomMapSource α R).app X).app Y =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (α.app X.unop)).app (R.obj Y) := rfl

def resolutionHomMapTarget (Q : C ⥤ (SimplexCategory ⥤ C)) {R R' : C ⥤ C} (β : R ⟶ R') :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q R ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom Q R' where
  app X := Functor.whiskerRight β (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (Q.obj X.unop))
  naturality {_ _} f := by
    ext Y n h
    change ((Q.map f.unop).app n.unop ≫ h) ≫ β.app Y =
      (Q.map f.unop).app n.unop ≫ (h ≫ β.app Y)
    exact Category.assoc _ _ _

@[simp]
lemma resolutionHomMapTarget_app (Q : C ⥤ (SimplexCategory ⥤ C)) {R R' : C ⥤ C} (β : R ⟶ R')
    (X : Cᵒᵖ) (Y : C) :
    ((resolutionHomMapTarget Q β).app X).app Y =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (Q.obj X.unop)).map (β.app Y) := rfl

end SerrePositivity.HomotopyFunctionComplex

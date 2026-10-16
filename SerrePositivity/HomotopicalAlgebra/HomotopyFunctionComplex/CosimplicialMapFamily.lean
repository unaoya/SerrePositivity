module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.DiagonalHomComposition

/-! # Simplicially parameterized maps between cosimplicial diagrams

Evaluation on the diagonal of a genuine double-Hom family supplies the
compatibility law. The construction has no model category assumptions.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C]

structure CosimplicialMapFamily (T : SSet.{v}) (D A : SimplexCategory ⥤ C) where
  app (n : SimplexCategoryᵒᵖ) : T.obj n → (D.obj n.unop ⟶ A.obj n.unop)
  naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (x : T.obj n) :
    D.map θ.unop ≫ app n x = app m (T.map θ x) ≫ A.map θ.unop

namespace CosimplicialMapFamily
variable {T U : SSet.{v}} {D A : SimplexCategory ⥤ C}

def ofMap (f : D ⟶ A) : CosimplicialMapFamily T D A where
  app n _ := f.app n.unop
  naturality θ _ := f.naturality θ.unop

def identity (A : SimplexCategory ⥤ C) : CosimplicialMapFamily T A A := ofMap (𝟙 A)

def reindex (a : CosimplicialMapFamily T D A) (f : U ⟶ T) : CosimplicialMapFamily U D A where
  app n x := a.app n (f.app n x)
  naturality θ x := by
    rw [a.naturality]
    have h := congrArg (fun k => k x) (f.naturality θ)
    exact congrArg (fun y => a.app _ y ≫ A.map θ.unop) h.symm

@[simp] lemma reindex_app (a : CosimplicialMapFamily T D A) (f : U ⟶ T)
    (n : SimplexCategoryᵒᵖ) (x : U.obj n) : (a.reindex f).app n x = a.app n (f.app n x) := rfl

/-- Evaluate an actual family of natural transformations in both simplex coordinates. -/
def ofDoubleHom {D : SimplexCategory ⥤ SimplexCategory ⥤ C} {A : SimplexCategory ⥤ C}
    (s : T ⟶ (cosimplicialHom D).obj A) :
    CosimplicialMapFamily T (DiagonalFrame.obj D) A where
  app n x := (s.app n x).app n.unop
  naturality {n m} θ x := by
    have hs := congrArg (fun k => k x) (s.naturality θ)
    change s.app m (T.map θ x) = D.map θ.unop ≫ s.app n x at hs
    change ((D.map θ.unop).app m.unop ≫ (D.obj n.unop).map θ.unop) ≫
      (s.app n x).app n.unop = (s.app m (T.map θ x)).app m.unop ≫ A.map θ.unop
    rw [hs]
    change _ = ((D.map θ.unop).app m.unop ≫ (s.app n x).app m.unop) ≫ A.map θ.unop
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k => (D.map θ.unop).app m.unop ≫ k)
        ((s.app n x).naturality θ.unop)).trans (Category.assoc _ _ _).symm)

@[simp] lemma ofDoubleHom_app {D : SimplexCategory ⥤ SimplexCategory ⥤ C}
    {A : SimplexCategory ⥤ C} (s : T ⟶ (cosimplicialHom D).obj A)
    (n : SimplexCategoryᵒᵖ) (x : T.obj n) :
    (ofDoubleHom s).app n x = (s.app n x).app n.unop := rfl

lemma ofDoubleHom_reindex {D : SimplexCategory ⥤ SimplexCategory ⥤ C}
    {A : SimplexCategory ⥤ C} (s : T ⟶ (cosimplicialHom D).obj A) (f : U ⟶ T) :
    ofDoubleHom (f ≫ s) = (ofDoubleHom s).reindex f := rfl

end CosimplicialMapFamily
end SerrePositivity.HomotopyFunctionComplex

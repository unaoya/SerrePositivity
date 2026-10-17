module
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # coneの比較射から三角形比較を組み立てる補助 -/
@[expose] public section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable {C T : Type*} [Category* C] [Category* T] [HasShift C ℤ] [HasShift T ℤ]

def coneTriangleMapIso (F : C ⥤ T) [F.CommShift ℤ]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
    {Z' : T} (g' : F.obj Y ⟶ Z') (h' : Z' ⟶ (F.obj X)⟦(1 : ℤ)⟧)
    (e : Z' ≅ F.obj Z) (hg : g' ≫ e.hom = F.map g)
    (hh : e.hom ≫ F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app X = h') :
    Triangle.mk (F.map f) g' h' ≅ F.mapTriangle.obj (Triangle.mk f g h) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (hg.trans (Category.id_comp _).symm)
    ((congrArg (fun k => h' ≫ k) ((shiftFunctor T (1 : ℤ)).map_id (F.obj X))).trans
      ((Category.comp_id _).trans hh.symm))

end SerrePositivity.DifferentialGraded

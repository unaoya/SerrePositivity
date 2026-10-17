module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FreePathResolution
public import Mathlib.CategoryTheory.NatIso

/-! # Singleton paths commute with exact object transports -/

@[expose] public section
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.QuiverPaths
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

lemma singleton_transport {X X' Y Y' : D} (hX : X' = X) (hY : Y = Y') (f : X ⟶ Y) :
    Quiver.Path.comp (@eqToHom (Paths D) (Paths.categoryPaths D).toCategoryStruct X' X hX)
      (Quiver.Path.comp f.toPath
        (@eqToHom (Paths D) (Paths.categoryPaths D).toCategoryStruct Y Y' hY)) =
        (eqToHom hX ≫ f ≫ eqToHom hY).toPath := by
  cases hX
  cases hY
  change Quiver.Path.comp Quiver.Path.nil (Quiver.Path.comp f.toPath Quiver.Path.nil) =
    (𝟙 X ≫ f ≫ 𝟙 Y).toPath
  simp only [Quiver.Path.nil_comp, Quiver.Path.comp_nil, Category.id_comp, Category.comp_id]

lemma map_copyObj_generator (F : C ⥤ D) (g : C → D) (h : ∀ X, F.obj X = g X)
    {X Y : C} (f : X ⟶ Y) :
    ((HomotopyFunctionComplex.FreePathResolution.map F).copyObj (fun X => g X)
      (fun X => eqToIso (h X))).map f.toPath =
        ((F.copyObj g (fun X => eqToIso (h X))).map f).toPath := by
  change Quiver.Path.comp
      (@eqToHom (Paths D) (Paths.categoryPaths D).toCategoryStruct (g X) (F.obj X) (h X).symm)
      (Quiver.Path.comp (F.map f).toPath
        (@eqToHom (Paths D) (Paths.categoryPaths D).toCategoryStruct (F.obj Y) (g Y) (h Y))) = _
  exact singleton_transport (h X).symm (h Y) (F.map f)

lemma counit_copy_singleton {X Y : D} (f : X ⟶ Y) :
    ((HomotopyFunctionComplex.FreePathResolution.counit D).copyObj (fun X => (X : D))
      (fun X => @Iso.refl.{v', u'} D inferInstance X)).map f.toPath = f := by
  simp only [Functor.copyObj, Iso.refl_inv, Iso.refl_hom, Category.id_comp]
  exact (@Category.comp_id D inferInstance X Y
    ((HomotopyFunctionComplex.FreePathResolution.counit D).map f.toPath)).trans
      (composePath_toPath f)

end SerrePositivity.QuiverPaths

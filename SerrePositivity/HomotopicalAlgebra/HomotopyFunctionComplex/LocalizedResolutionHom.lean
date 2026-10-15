module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionLiftIndependence

/-! # Source functoriality without functorial factorizations

Independent resolution lifts define a strict functor after localizing the
space-valued output. Its values retain the full actual mapping spaces. A
strict simplicial-set-valued functor on C itself is a further rectification
problem; it is not asserted here.
-/

@[expose] public section
universe v u vS uS
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  {H : Type uS} [Category.{vS} H] (L : SSet.{v} ⥤ H)
  [L.IsLocalization (weakEquivalences SSet.{v})]

/-- Genuine source functoriality in Ho(SSet), with fibrant target parameter. -/
def localizedResolutionHom : Cᵒᵖ ⥤ FibrantObject C ⥤ H where
  obj X := (ResolutionObject.hom.obj (Opposite.op (ResolutionObject.ofObject X.unop))) ⋙ L
  map f := Functor.whiskerRight
    (ResolutionObject.hom.map (ResolutionObject.lift
      (X := ResolutionObject.ofObject _) (Y := ResolutionObject.ofObject _) f.unop).op) L
  map_id X := by
    ext Y
    change L.map ((ResolutionObject.hom.map
      (ResolutionObject.lift (X := ResolutionObject.ofObject X.unop)
        (Y := ResolutionObject.ofObject X.unop) (𝟙 X).unop).op).app Y) = 𝟙 _
    trans L.map ((ResolutionObject.hom.map (𝟙 _)).app Y)
    · exact ResolutionObject.hom_map_eq_of_base_eq hcof L
        (ResolutionObject.lift (X := ResolutionObject.ofObject X.unop)
          (Y := ResolutionObject.ofObject X.unop) (𝟙 X).unop).op (𝟙 _) rfl Y
    simp
  map_comp {X Y Z} f g := by
    ext T
    change L.map ((ResolutionObject.hom.map
      (ResolutionObject.lift (X := ResolutionObject.ofObject Z.unop)
        (Y := ResolutionObject.ofObject X.unop) (f ≫ g).unop).op).app T) = _
    trans L.map ((ResolutionObject.hom.map
      ((ResolutionObject.lift (X := ResolutionObject.ofObject Y.unop)
        (Y := ResolutionObject.ofObject X.unop) f.unop).op ≫
       (ResolutionObject.lift (X := ResolutionObject.ofObject Z.unop)
        (Y := ResolutionObject.ofObject Y.unop) g.unop).op)).app T)
    · exact ResolutionObject.hom_map_eq_of_base_eq hcof L
        (ResolutionObject.lift (X := ResolutionObject.ofObject Z.unop)
          (Y := ResolutionObject.ofObject X.unop) (f ≫ g).unop).op
        ((ResolutionObject.lift (X := ResolutionObject.ofObject Y.unop)
          (Y := ResolutionObject.ofObject X.unop) f.unop).op ≫
         (ResolutionObject.lift (X := ResolutionObject.ofObject Z.unop)
          (Y := ResolutionObject.ofObject Y.unop) g.unop).op) rfl T
    simp only [Functor.map_comp, NatTrans.comp_app, Functor.whiskerRight_app]

@[simp]
lemma localizedResolutionHom_obj (X : Cᵒᵖ) (Y : FibrantObject C) :
    ((localizedResolutionHom hcof L).obj X).obj Y =
      L.obj ((cosimplicialHom (Reedy.cosimplicialResolution X.unop).obj).obj Y.obj) := rfl

lemma localizedResolutionHom_map_source_isIso {X X' : Cᵒᵖ}
    (f : X ⟶ X') (hf : weakEquivalences C f.unop) (Y : FibrantObject C) :
    IsIso (((localizedResolutionHom hcof L).map f).app Y) :=
  Localization.inverts L (weakEquivalences SSet.{v}) _
    (ResolutionObject.hom_map_source_weakEquivalence hcof _ hf Y)

lemma localizedResolutionHom_map_target_isIso (X : Cᵒᵖ)
    {Y Y' : FibrantObject C} (f : Y ⟶ Y') (hf : weakEquivalences C f.hom) :
    IsIso (((localizedResolutionHom hcof L).obj X).map f) :=
  Localization.inverts L (weakEquivalences SSet.{v}) _
    (ResolutionObject.hom_map_target_weakEquivalence hcof _ f hf)

end SerrePositivity.HomotopyFunctionComplex

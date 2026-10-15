module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ExtensionFunctor

/-! # Returning an attached diagram to the usual degree restriction

When degree distinguishes objects, adjoining j to the objects below its
degree gives the whole closed degree restriction. This applies to Δ and
Δop. The construction preserves every old object and every old map.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) (j : J)

abbrev lowerToUpper : Lower r (r.deg j) ⥤ Upper r (r.deg j) :=
  ObjectProperty.ιOfLE (fun _ h ↦ h.le)

abbrev degreeIndexObj (x : Upper r (r.deg j)) : Adjoin r j :=
  if h : r.deg x.obj < r.deg j then some ⟨x.obj, h⟩ else none

lemma degreeIndexObj_eq (hinj : Function.Injective r.deg) (x : Upper r (r.deg j)) :
    adjoinObj r j (degreeIndexObj r j x) = x.obj := by
  by_cases h : r.deg x.obj < r.deg j
  · simp only [degreeIndexObj, dite_eq_left h, adjoinObj]
  · simp only [degreeIndexObj, dite_eq_right h, adjoinObj]
    exact (hinj (le_antisymm x.property (le_of_not_gt h))).symm

def degreeIndex (hinj : Function.Injective r.deg) : Upper r (r.deg j) ⥤ Adjoin r j where
  obj := degreeIndexObj r j
  map {x y} f := InducedCategory.homMk
    (eqToHom (degreeIndexObj_eq r j hinj x) ≫ f.hom ≫
      eqToHom (degreeIndexObj_eq r j hinj y).symm)
  map_id x := by
    apply InducedCategory.hom_ext
    simp only [InducedCategory.homMk_hom, ObjectProperty.FullSubcategory.id_hom,
      Category.id_comp, eqToHom_trans,
      eqToHom_refl, InducedCategory.id_hom]
  map_comp f g := by
    apply InducedCategory.hom_ext
    simp only [InducedCategory.homMk_hom, ObjectProperty.FullSubcategory.comp_hom,
      InducedCategory.comp_hom,
      Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

lemma degreeIndex_obj_lower (x : Lower r (r.deg j)) :
    degreeIndexObj r j ((lowerToUpper r j).obj x) = some x := by
  change (if h : r.deg x.obj < r.deg j then some ⟨x.obj, h⟩ else none) = some x
  simp only [dite_eq_left x.property]

lemma degreeIndex_map_lower (hinj : Function.Injective r.deg)
    {x y : Lower r (r.deg j)} (f : x ⟶ y) :
    (degreeIndex r j hinj).map ((lowerToUpper r j).map f) =
      eqToHom (degreeIndex_obj_lower r j x) ≫ (adjoinLower r j).map f ≫
        eqToHom (degreeIndex_obj_lower r j y).symm := by
  apply InducedCategory.hom_ext
  simp only [degreeIndex, lowerToUpper, ObjectProperty.ιOfLE_map,
    ObjectProperty.homMk_hom, InducedCategory.comp_hom, InducedCategory.eqToHom_hom,
    adjoinLower, InducedCategory.homMk_hom]

lemma conjugate_eqToHom {D : Type*} [Category* D] {w x y z : D}
    (hx : w = x) (hy : z = y) (f : x ⟶ y) :
    (eqToHom hx ≫ f ≫ eqToHom hy.symm) ≫ eqToHom hy = eqToHom hx ≫ f := by
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

namespace BoundaryExtension
variable {r j} {C : Type u'} [Category.{v'} C] {H : Lower r (r.deg j) ⥤ C}
  (d : BoundaryExtension r j H) (hinj : Function.Injective r.deg)

abbrev degreeExtension : Upper r (r.deg j) ⥤ C := degreeIndex r j hinj ⋙ d.toFunctor

/-- The entire previous diagram is retained up to the canonical identity-component iso. -/
def degreeRestrictionIso : lowerToUpper r j ⋙ d.degreeExtension hinj ≅ H :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (NatIso.ofComponents (fun x ↦ eqToIso (degreeIndex_obj_lower r j x)) (fun f ↦ by
        change (degreeIndex r j hinj).map ((lowerToUpper r j).map f) ≫
          eqToHom (degreeIndex_obj_lower r j _) =
          eqToHom (degreeIndex_obj_lower r j _) ≫ (adjoinLower r j).map f
        rw [degreeIndex_map_lower]
        exact conjugate_eqToHom (D := Adjoin r j) _ _ _))
      d.toFunctor ≪≫ d.restrictionIso

end BoundaryExtension
end SerrePositivity.Reedy

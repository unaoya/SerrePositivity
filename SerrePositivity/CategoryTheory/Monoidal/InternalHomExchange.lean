module

public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Exchanging the two variables of an iterated internal Hom

The isomorphism uses actual internal currying and the braiding. Its double
uncurry formula records the two evaluations explicitly for model-theoretic
applications; no model structure is involved here.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.InternalHomExchange
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]

def iso (X K Z : C) : (ihom X).obj ((ihom K).obj Z) ≅ (ihom K).obj ((ihom X).obj Z) :=
  (ihomCurryIso K X Z).symm ≪≫
    (MonoidalClosed.internalHom.mapIso (β_ X K).op).app Z ≪≫ ihomCurryIso X K Z

omit [BraidedCategory C] in
lemma doubleUncurry_comp_ihomCurry (X K Z A : C) (f : A ⟶ (ihom (X ⊗ K)).obj Z) :
    uncurry (uncurry (f ≫ ihomCurry X K Z)) = (α_ X K A).inv ≫ uncurry f := by
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_uncurry_ihomCurry,
    associator_inv_naturality_right_assoc]
  rw [uncurry_eq]

lemma doubleUncurry_iso_hom (X K Z : C) :
    uncurry (uncurry (iso X K Z).hom) =
      (α_ X K ((ihom X).obj ((ihom K).obj Z))).inv ≫
        (β_ X K).hom ▷ (ihom X).obj ((ihom K).obj Z) ≫
          (α_ K X ((ihom X).obj ((ihom K).obj Z))).hom ≫
            K ◁ (ihom.ev X).app ((ihom K).obj Z) ≫ (ihom.ev K).app Z := by
  change uncurry (uncurry
    (ihomUncurry K X Z ≫ (pre (β_ X K).hom).app Z ≫ ihomCurry X K Z)) = _
  rw [← Category.assoc, doubleUncurry_comp_ihomCurry, uncurry_pre_app, uncurry_ihomUncurry]

lemma doubleUncurry_map_exchange (X K Z Y : C) (f : Y ⟶ (ihom K).obj Z) :
    uncurry (uncurry ((ihom X).map f ≫ (iso X K Z).hom)) =
      (α_ X K ((ihom X).obj Y)).inv ≫
        (β_ X K).hom ▷ (ihom X).obj Y ≫
          (α_ K X ((ihom X).obj Y)).hom ≫ K ◁ (ihom.ev X).app Y ≫ uncurry f := by
  rw [uncurry_natural_left, uncurry_natural_left, doubleUncurry_iso_hom,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc]
  have hn : X ◁ (ihom X).map f ≫ (ihom.ev X).app ((ihom K).obj Z) =
      (ihom.ev X).app Y ≫ f := (ihom.ev X).naturality f
  rw [← whiskerLeft_comp_assoc, hn, whiskerLeft_comp, Category.assoc, uncurry_eq]

end SerrePositivity.InternalHomExchange

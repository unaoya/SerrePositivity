module
public import SerrePositivity.DifferentialGraded.Complexes.HomMapEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.UnitScalarEvaluation
public import SerrePositivity.DifferentialGraded.Bimodule.ActionEvaluation
public import Mathlib.Data.ZMod.Basic

/-! # 全Hom自然性のための合成・作用評価の検査 -/
@[expose] public section
universe u
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

example {X Y Z : Complex A} (g : Cochain X Y (-1)) (f : Y ⟶ Z) (x : X.X 1) :
    (g.comp (Cochain.ofHom f) (add_zero (-1))).v 1 0 (by decide) x =
      f.f 0 (g.v 1 0 (by decide) x) :=
  cochain_comp_ofHom_apply g f (by decide) x

example {X Y Z : Complex A} (f : X ⟶ Y) (g : Cochain Y Z 1) (x : X.X (-1)) :
    ((Cochain.ofHom f).comp g (zero_add 1)).v (-1) 0 (by decide) x =
      g.v (-1) 0 (by decide) (f.f (-1) x) :=
  cochain_ofHom_comp_apply f g (by decide) x

example {X Y : Complex (ZMod 2)} (f : X ⟶ Y) (x : X.X (-1)) :
    f.f (-1) (((-1 : ℤ).negOnePow) • x) =
      ((-1 : ℤ).negOnePow) • f.f (-1) x :=
  chain_units_smul f (-1) _ x

#print axioms element_square
#print axioms cochain_comp_ofHom_apply
#print axioms cochain_ofHom_comp_apply
#print axioms hom_naturality_of_apply
#print axioms chain_units_smul
#print axioms Bimodule.leftCochain_apply

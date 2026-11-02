module
public import SerrePositivity.DifferentialGraded.Tensor.Enriched


public import Mathlib.Data.ZMod.Basic

/-! # M/N/Tの全Hom自然性の統合検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Opposite SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (M : RightModule A D) (N N' : LeftModule A D) (T : Complex A) :
    (leftHomMap A D M N N' ≫ (homContravariantDG A T).map
      (op (obj A D M N')) (op (obj A D M N))) ≫
      homPostcompose (homComplex A (obj A D M N') T) (enrichedTensorHomIso A D M N T).hom =
    (homRightContraHomMap A D N N' T ≫ modulePostcompositionMap A D M
      (homRightModule A D N' T) (homRightModule A D N T)) ≫
      homPrecompose (enrichedTensorHomIso A D M N' T).hom
        (moduleHom A D M (homRightModule A D N T)) :=
  enrichedTensorHomIso_left_naturality A D M N N' T

example (M : RightModule (ZMod 2) PUnit.{1}) (N N' : LeftModule (ZMod 2) PUnit.{1})
    (T : Complex (ZMod 2)) :
    (leftHomMap (ZMod 2) PUnit.{1} M N N' ≫ (homContravariantDG (ZMod 2) T).map
      (op (obj (ZMod 2) PUnit.{1} M N')) (op (obj (ZMod 2) PUnit.{1} M N))) ≫
      homPostcompose (homComplex (ZMod 2) (obj (ZMod 2) PUnit.{1} M N') T)
        (enrichedTensorHomIso (ZMod 2) PUnit.{1} M N T).hom =
    (homRightContraHomMap (ZMod 2) PUnit.{1} N N' T ≫ modulePostcompositionMap (ZMod 2) PUnit.{1} M
      (homRightModule (ZMod 2) PUnit.{1} N' T) (homRightModule (ZMod 2) PUnit.{1} N T)) ≫
      homPrecompose (enrichedTensorHomIso (ZMod 2) PUnit.{1} M N' T).hom
        (moduleHom (ZMod 2) PUnit.{1} M (homRightModule (ZMod 2) PUnit.{1} N T)) :=
  enrichedTensorHomIso_left_naturality (ZMod 2) PUnit.{1} M N N' T

#print axioms enrichedTensorHomIso_source_naturality
#print axioms enrichedTensorHomIso_target_naturality
#print axioms enrichedTensorHomIso_left_naturality

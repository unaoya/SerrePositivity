module
public import SerrePositivity.DifferentialGraded.Tensor.EnrichedHomSource
public import SerrePositivity.DifferentialGraded.Tensor.EnrichedHomTarget
public import Mathlib.Data.ZMod.Basic

/-! # 豊穣tensor–Hom同型の右加群変数の反変自然性の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Opposite SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (M M' : RightModule A D) (N : LeftModule A D) (T : Complex A) :
    (rightHomMap A D M M' N ≫ (homContravariantDG A T).map
      (op (obj A D M' N)) (op (obj A D M N))) ≫
      homPostcompose (homComplex A (obj A D M' N) T) (enrichedTensorHomIso A D M N T).hom =
    modulePrecompositionMap A D M M' (homRightModule A D N T) ≫
      homPrecompose (enrichedTensorHomIso A D M' N T).hom
        (moduleHom A D M (homRightModule A D N T)) :=
  enrichedTensorHomIso_source_naturality A D M M' N T

example (M M' : RightModule (ZMod 2) PUnit.{1}) (N : LeftModule (ZMod 2) PUnit.{1})
    (T : Complex (ZMod 2)) :
    (rightHomMap (ZMod 2) PUnit.{1} M M' N ≫ (homContravariantDG (ZMod 2) T).map
      (op (obj (ZMod 2) PUnit.{1} M' N)) (op (obj (ZMod 2) PUnit.{1} M N))) ≫
      homPostcompose (homComplex (ZMod 2) (obj (ZMod 2) PUnit.{1} M' N) T)
        (enrichedTensorHomIso (ZMod 2) PUnit.{1} M N T).hom =
    modulePrecompositionMap (ZMod 2) PUnit.{1} M M' (homRightModule (ZMod 2) PUnit.{1} N T) ≫
      homPrecompose (enrichedTensorHomIso (ZMod 2) PUnit.{1} M' N T).hom
        (moduleHom (ZMod 2) PUnit.{1} M (homRightModule (ZMod 2) PUnit.{1} N T)) :=
  enrichedTensorHomIso_source_naturality (ZMod 2) PUnit.{1} M M' N T

#print axioms enrichedTensorHomIso_source_naturality

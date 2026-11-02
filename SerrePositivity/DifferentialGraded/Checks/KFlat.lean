module
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 非有界の相対K-flat性の入口とretract閉性 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (x : D) (N : LeftModule A D) (hN : leftModuleAcyclic A D N) :
    (BalancedTensor.obj A D (representable A x) N).Acyclic :=
  representable_relativeKFlat A D x N hN

example (x : D) (M : RightModule A D)
    (e : Retract (ForgetEnrichment.of (Complex A) M)
      (ForgetEnrichment.of (Complex A) (representable A x))) :
    moduleRelativeKFlat A D M :=
  moduleRelativeKFlat_of_retract A D e (representable_relativeKFlat A D x)

example (x : PUnit.{1}) : moduleRelativeKFlat (ZMod 2) PUnit.{1} (representable (ZMod 2) x) :=
  representable_relativeKFlat (ZMod 2) PUnit.{1} x

#print axioms complexKFlat
#print axioms complexKFlat_of_iso
#print axioms complex_acyclic_of_retract
#print axioms complexKFlat_of_retract
#print axioms leftModuleAcyclic
#print axioms moduleRelativeKFlat
#print axioms representable_relativeKFlat
#print axioms moduleRelativeKFlat_of_iso
#print axioms moduleRelativeKFlat_of_retract

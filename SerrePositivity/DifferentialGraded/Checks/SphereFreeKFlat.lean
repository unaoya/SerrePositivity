module
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 自由tensor評価とsphere-freeの相対K-flat性の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (N : LeftModule A D) (x : D) (K : Complex A) :
    BalancedTensor.obj A D (ForgetEnrichment.to (Complex A) ((freeAt x).obj K)) N ≅
      K ⊗ N.obj x :=
  BalancedTensor.freeTensorIso A D N x K

example (x : D) : moduleRelativeKFlat A D
    (ForgetEnrichment.to (Complex A) (freeSphere A D x (-1))) :=
  freeSphere_relativeKFlat A D x (-1)

example (M : ModuleCategory A D) (S : ModuleSphereFreePresentation A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) :=
  sphereFreePresentation_relativeKFlat A D S

example (x : PUnit.{1}) : moduleRelativeKFlat (ZMod 2) PUnit.{1}
    (ForgetEnrichment.to (Complex (ZMod 2)) (freeSphere (ZMod 2) PUnit.{1} x 1)) :=
  freeSphere_relativeKFlat (ZMod 2) PUnit.{1} x 1

#print axioms BalancedTensor.homRightEvaluationIso
#print axioms BalancedTensor.freeTensorFunctorIso
#print axioms BalancedTensor.freeTensorIso
#print axioms BalancedTensor.freeTensorIso_naturality
#print axioms freeAt_relativeKFlat
#print axioms complexSphere_kFlat
#print axioms freeSphere_relativeKFlat
#print axioms sphereFreePresentation_relativeKFlat

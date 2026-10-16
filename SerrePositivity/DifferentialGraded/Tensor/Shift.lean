module
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift
public import SerrePositivity.DifferentialGraded.Tensor.Homotopy
public import SerrePositivity.DifferentialGraded.Tensor.KFlatCriterion
public import SerrePositivity.DifferentialGraded.Module.ShiftCoherence

/-! # balanced tensorの右加群shift比較と相対K-flatのshift閉性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実際のbalanced tensorは右加群の整数shiftを通常の複体shiftへ送る。 -/
def rightTensorShiftIso (L : LeftModule A D) (s : ℤ) (M : RightModule A D) :
    obj A D (shiftModule s M) L ≅ (obj A D M L)⟦s⟧ :=
  DGFunctor.moduleShiftImageIso A D (rightTensorDG A D L) s M

end BalancedTensor

open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 任意整数shiftは相対K-flat性を保つ。 -/
lemma moduleRelativeKFlat_shift {M : RightModule A D} (hM : moduleRelativeKFlat A D M) (s : ℤ) :
    moduleRelativeKFlat A D (shiftModule s M) := by
  intro L hL
  exact cochainAcyclic_of_iso (cochainAcyclic_shift (hM L hL) s)
    (BalancedTensor.rightTensorShiftIso A D L s M).symm

/-- 閉零加群圏の既存HasShiftについても同じ閉性が成り立つ。 -/
lemma moduleRelativeKFlat_shiftObj {M : ModuleCategory A D}
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) (s : ℤ) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (M⟦s⟧)) :=
  moduleRelativeKFlat_shift A D hM s

end SerrePositivity.DifferentialGraded

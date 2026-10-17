module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedKoszulReduction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerReduction
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Regular.SMul

/-! # 正則な加群上のスカラー錐と通常の冪商

正則性は加群上だけに要求する。元環での正則性や平坦性を追加しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (a : R) (M : ModuleCat.{u} R)

/-- 加群上での正則性は、その全ての冪商の実短完全列を与える。 -/
theorem modulePowerReductionShortComplex_shortExact_of_regular
    (hM : IsSMulRegular M a) (n : ℕ) :
    (modulePowerReductionShortComplex a M n).ShortExact := by
  have : Mono (a ^ n • 𝟙 M) := (ModuleCat.mono_iff_injective _).mpr (hM.pow n)
  exact ⟨modulePowerReductionShortComplex_exact a M n⟩

/-- 実スカラー錐を元の通常商へ比較する。正則性は M 上だけでよい。 -/
def derivedScalarConeModuleQuotientIso (hM : IsSMulRegular M a) (n : ℕ) :
    (derivedScalarConeFunctor R (a ^ n)).obj ((moduleObjectFunctor R).obj M) ≅
      (moduleObjectFunctor R).obj (modulePowerReduction a M n) := by
  let F := CochainComplex.singleFunctor (ModuleCat.{u} R) 0
  let S := (modulePowerReductionShortComplex a M n).map F
  have hS : S.ShortExact :=
    (modulePowerReductionShortComplex_shortExact_of_regular a M hM n).map_of_exact F
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  exact (derivedScalarConeComparison R (a ^ n)).app (F.obj M) ≪≫
    eqToIso (by
      change DerivedCategory.Q.obj (CochainComplex.mappingCone (smulId (a ^ n) (F.obj M))) =
        DerivedCategory.Q.obj (CochainComplex.mappingCone (F.map (a ^ n • 𝟙 M)))
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
      rfl) ≪≫
    asIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S))

end SerrePositivity.DerivedCompletion

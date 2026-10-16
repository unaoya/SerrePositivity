module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTorAlgebraTower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarRestriction

/-! # Completeness and the original ideal action on the two Tor-tower endpoints

Neither endpoint is discarded. Stage annihilation is a conditional input;
there is no assumption that the ideal is idempotent in the coefficient ring.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R : Type u} [CommRing R] (a : R)
  (C : Type u) [CommRing C] [Algebra R C] (M : ModuleCat.{u} R) (i : ℕ)
  (B : Type u) [CommRing B] (ψ : B →+* C) (I : Ideal B)
  (hTor : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
    (∀ x : N, a ^ k • x = 0) → ∀ b ∈ I, torCoefficientScalarEndomorphism C N i (ψ b) = 0)

include hTor in
lemma modulePowerTorAlgebraStage_annihilated (n : ℕ) :
    I ≤ Module.annihilator B ((ModuleCat.restrictScalars ψ).obj
      (modulePowerTorAlgebraTower a C M i n)) := by
  intro b hb
  rw [Module.mem_annihilator]
  have ht : ∀ x : modulePowerReduction a M n, a ^ (n + 1) • x = 0 := by
    intro x
    rw [pow_succ', mul_smul, modulePowerReduction_pow_smul_zero, smul_zero]
  exact (torAlgebraComparison_scalar_zero_iff_forall (modulePowerReduction a M n) i (ψ b)).mp
    (hTor _ (n + 1) (Nat.succ_pos _) ht b hb)

include hTor in
lemma modulePowerTorAlgebraLimit_annihilated :
    I ≤ Module.annihilator B ((ModuleCat.restrictScalars ψ).obj
      (modulePowerTorAlgebraLimit a C M i)) := by
  intro b hb
  rw [Module.mem_annihilator]
  intro x
  apply Subtype.ext
  funext n
  exact Module.mem_annihilator.mp
    (modulePowerTorAlgebraStage_annihilated a C M i B ψ I hTor n hb) (x.val n)

include hTor in
lemma modulePowerTorAlgebraLimOne_annihilated :
    I ≤ Module.annihilator B ((ModuleCat.restrictScalars ψ).obj
      (modulePowerTorAlgebraLimOne a C M i)) := by
  intro b hb
  rw [Module.mem_annihilator]
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ y =>
    change Submodule.Quotient.mk ((ψ b) • y) = 0
    have hy : (ψ b) • y = 0 := by
      funext n
      exact Module.mem_annihilator.mp
        (modulePowerTorAlgebraStage_annihilated a C M i B ψ I hTor n hb) (y n)
    rw [hy]
    rfl

/-- The limit endpoint is complete over any original coefficient source B→C. -/
lemma modulePowerTorAlgebraLimit_isModuleComplete_restrict (p : ℕ) :
    IsModuleComplete B (p : B) ((ModuleCat.restrictScalars ψ).obj
      (modulePowerTorAlgebraLimit (p : R) C M i)) := by
  letI : Algebra B C := ψ.toAlgebra
  let X := modulePowerTorAlgebraLimit (p : R) C M i
  letI : Module B X := Module.compHom X ψ
  letI : IsScalarTower B C X := IsScalarTower.of_algebraMap_smul fun r x => rfl
  have hc : IsModuleComplete C (algebraMap B C (p : B)) X := by
    simpa only [map_natCast] using modulePowerTorAlgebraLimit_isModuleComplete (p : R) C M i
  exact (isModuleComplete_algebraMap_iff B C (p : B) X).mp hc

/-- The lim¹ endpoint is complete as well, without a surjectivity or vanishing hypothesis. -/
lemma modulePowerTorAlgebraLimOne_isModuleComplete_restrict (p : ℕ) :
    IsModuleComplete B (p : B) ((ModuleCat.restrictScalars ψ).obj
      (modulePowerTorAlgebraLimOne (p : R) C M i)) := by
  letI : Algebra B C := ψ.toAlgebra
  let X := modulePowerTorAlgebraLimOne (p : R) C M i
  letI : Module B X := Module.compHom X ψ
  letI : IsScalarTower B C X := IsScalarTower.of_algebraMap_smul fun r x => rfl
  have hc : IsModuleComplete C (algebraMap B C (p : B)) X := by
    simpa only [map_natCast] using modulePowerTorAlgebraLimOne_isModuleComplete (p : R) C M i
  exact (isModuleComplete_algebraMap_iff B C (p : B) X).mp hc

end SerrePositivity.DerivedCompletion

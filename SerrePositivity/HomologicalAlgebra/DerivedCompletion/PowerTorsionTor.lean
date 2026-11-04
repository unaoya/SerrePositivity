module

public import SerrePositivity.HomologicalAlgebra.DerivedTensorLinear
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedModule
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IdealExtension
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TorAlgebraComplete
public import SerrePositivity.HomologicalAlgebra.TorFiniteCoefficients

/-! # 冪ねじれの検査からの Tor の消滅

## 概要

完備化の同値と実際の冪ねじれの導来対象とのテンソル積が同値のままであることを示し（`completionEquivalence_tensor_powerTorsion_isIso`）、冪ねじれの検査と完備な almost 拡大閉性から全ての Tor の消滅を（`tor_eq_zero_of_power_torsion_and_complete_extensions`）、具体的な conormal（商の Tor₁）の入力からも得る。

## 方針

比較は与えられた射の元のテンソル積。左因子の正則性・平坦性・有限生成性・完備性は仮定しない。

## 規約

拡大閉性は明示的な数学的入力で、BS 著者版 Prop 10.2 の使う部分に当たる。旧 `PowerTorsionTensor`・`PowerTorsionTorExtension`・`PowerTorsionTorConormal`（HA の Tor の側へ移す候補、refactor-plan §3.5.1）。

## 使われ方

BhattScholze の Almost、CLMST の全加群 Tor。
-/

@[expose] public noncomputable section

universe u

section PowerTorsionTensorPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R)
local notation "D" => DerivedCategory.Minus (ModuleCat R)

/-- A power killing a derived tensor factor kills the same power on the whole tensor. -/
lemma derivedTensor_scalar_pow_zero_right (X Y : D) (n : ℕ)
    (hY : a ^ n • 𝟙 Y = 0) : a ^ n • 𝟙 (X ⊗ Y) = 0 := by
  calc
    a ^ n • 𝟙 (X ⊗ Y) = (𝟙 X) ⊗ₘ (a ^ n • 𝟙 Y) := by
      rw [derivedTensorHom_smul_right, id_tensorHom_id]
    _ = 0 := by rw [hY]; simp

/-- The tensor is complete because its actual identity has a power-torsion scalar action. -/
lemma derivedTensor_isComplete_of_right_scalar_pow_zero (X Y : D) (n : ℕ)
    (hY : a ^ n • 𝟙 Y = 0) : IsComplete R a (X ⊗ Y).obj := by
  apply isComplete_of_scalar_pow_zero R a _ n
  exact congrArg (fun f : X ⊗ Y ⟶ X ⊗ Y => f.hom)
    (derivedTensor_scalar_pow_zero_right R a X Y n hY)

/-- A completion equivalence becomes an actual isomorphism after tensoring with a
power-torsion derived object; the original morphism is retained. -/
lemma completionEquivalence_tensor_powerTorsion_isIso {X X' : D} (f : X ⟶ X')
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom))
    (Y : D) (n : ℕ) (hY : a ^ n • 𝟙 Y = 0) : IsIso (f ▷ Y) := by
  have h := completionEquivalence_whiskerRight R a f hf Y
  apply boundedAbove_isIso_of_koszul_of_isComplete R a (f ▷ Y)
    (derivedTensor_isComplete_of_right_scalar_pow_zero R a X Y n hY)
    (derivedTensor_isComplete_of_right_scalar_pow_zero R a X' Y n hY)
  exact fun k => derivedScalarCone_map_isIso_of_completion R a (f ▷ Y).hom h k

/-- In particular the original completion unit is inverted by a power-torsion tensor test. -/
lemma completionUnit_tensor_powerTorsion_isIso (X Y : D) (n : ℕ)
    (hY : a ^ n • 𝟙 Y = 0) :
    IsIso ((boundedAboveDerivedCompletionUnit R a).app X ▷ Y) :=
  completionEquivalence_tensor_powerTorsion_isIso R a _
    (derivedComplexCompletionFunctor_map_unit_isIso R a X.obj) Y n hY

/-- Arbitrary power-torsion module tests invert the same original completion unit. -/
lemma completionUnit_tensor_module_powerTorsion_isIso (X : D) (N : ModuleCat.{u} R)
    (n : ℕ) (hN : ∀ x : N, a ^ n • x = 0) :
    IsIso ((boundedAboveDerivedCompletionUnit R a).app X ▷
      boundedAboveDerivedSingleFunctor.obj N) := by
  apply completionUnit_tensor_powerTorsion_isIso R a X _ n
  apply InducedCategory.hom_ext
  change a ^ n • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj N) = 0
  have h : a ^ n • 𝟙 N = 0 := by ext x; exact hN x
  have hs := congrArg (DerivedCategory.singleFunctor (ModuleCat R) 0).map h
  simpa only [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] using hs

end SerrePositivity.DerivedCompletion

end PowerTorsionTensorPart

section PowerTorsionTorExtensionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
  (p : ℕ) (C : Type u) [CommRing C] [Algebra R C]
  (B : Type u) [CommRing B] (ψ : B →+* C) (I : Ideal B)
  (hC : IsModuleComplete R (p : R) (ModuleCat.of R C))
  (hExt : CompleteIdealExtensionClosed B (p : B) I)
  (hTor : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
    (∀ x : N, (p : R) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
      ∀ b ∈ I, torCoefficientScalarEndomorphism C N j (ψ b) = 0)

include hC hExt hTor in
/-- The actual coefficient-linear Milnor sequence supplies almost zero for finite tests. -/
lemma finite_tor_eq_zero_of_power_torsion_and_complete_extensions
    (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℕ) (hi : 0 < i)
    (b : B) (hb : b ∈ I) : torCoefficientScalarEndomorphism C M i (ψ b) = 0 := by
  let S := torAlgebraMilnorShortComplexOver (p : R) C M hC i B ψ
  have hs : S.ShortExact := torAlgebraMilnorShortComplexOver_shortExact (p : R) C M hC i B ψ
  have h₁ : IsModuleComplete B (p : B) S.X₁ :=
    modulePowerTorAlgebraLimOne_isModuleComplete_restrict C M (i + 1) B ψ p
  have h₂ : IsModuleComplete B (p : B) S.X₂ :=
    torAlgebra_isModuleComplete_restrict_of_finite C M B ψ p hC i
  have h₃ : IsModuleComplete B (p : B) S.X₃ :=
    modulePowerTorAlgebraLimit_isModuleComplete_restrict C M i B ψ p
  have ha₁ : I ≤ Module.annihilator B S.X₁ :=
    modulePowerTorAlgebraLimOne_annihilated (p : R) C M (i + 1) B ψ I
      (fun N k hk hN => hTor N k hk hN (i + 1) (Nat.succ_pos _))
  have ha₃ : I ≤ Module.annihilator B S.X₃ :=
    modulePowerTorAlgebraLimit_annihilated (p : R) C M i B ψ I
      (fun N k hk hN => hTor N k hk hN i hi)
  have ha := hExt S hs h₁ h₂ h₃ ha₁ ha₃
  exact (torAlgebraComparison_restricted_annihilator_iff B ψ I M i).mpr ha b hb

include hC hExt hTor in
/-- The full original test quantifiers: arbitrary modules, all positive Tor and every ideal element. -/
lemma tor_eq_zero_of_power_torsion_and_complete_extensions
    (M : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) (b : B) (hb : b ∈ I) :
    torCoefficientScalarEndomorphism C M i (ψ b) = 0 := by
  apply torCoefficientScalarEndomorphism_eq_zero_of_finite C i (ψ b) _ M
  intro N hN
  letI := hN
  exact finite_tor_eq_zero_of_power_torsion_and_complete_extensions p C B ψ I hC hExt hTor N i hi b hb

end SerrePositivity.DerivedCompletion

end PowerTorsionTorExtensionPart

section PowerTorsionTorConormalPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]
  (p : ℕ) (C : Type u) [CommRing C] [Algebra R C]
  (B : Type u) [CommRing B] (ψ : B →+* C) (I : Ideal B)
  (hC : IsModuleComplete R (p : R) (ModuleCat.of R C))
  (hTor : ∀ (N : ModuleCat.{u} R) (k : ℕ), 0 < k →
    (∀ x : N, (p : R) ^ k • x = 0) → ∀ j : ℕ, 0 < j →
      ∀ b ∈ I, torCoefficientScalarEndomorphism C N j (ψ b) = 0)

include hC hTor in
lemma tor_eq_zero_of_power_torsion_and_quotientTorOne
    (hQ : Function.Surjective
      (fun x : TorModule B 1 (B ⧸ I) (B ⧸ I) => (p : B) • x))
    (M : ModuleCat.{u} R) (i : ℕ) (hi : 0 < i) (b : B) (hb : b ∈ I) :
    torCoefficientScalarEndomorphism C M i (ψ b) = 0 :=
  tor_eq_zero_of_power_torsion_and_complete_extensions p C B ψ I hC
    (completeIdealExtensionClosed_of_quotientTorOne_surjective (p : B) I hQ) hTor M i hi b hb

end SerrePositivity.DerivedCompletion

end PowerTorsionTorConormalPart

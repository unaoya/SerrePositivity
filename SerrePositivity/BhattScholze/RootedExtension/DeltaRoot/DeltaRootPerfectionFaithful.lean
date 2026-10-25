module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootPerfectionResidueFlat

/-! # 実δ完全化の標準剰余の忠実性とp完全忠実平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open TensorProduct
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A) (hD : D.IsPerfect)
variable (w : Aˣ) (hw : (w : A) = D.delta (p : A))
attribute [local instance] deltaRootPerfectionStageAlgebra deltaRootPerfectionAlgebra
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "F" => deltaAdjoinDivisionStructure E (p : P)
  (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "Raw" => DeltaAdjoinDivision E (p : P)
  (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "C" => DeltaPerfection F
local notation "S" => DeltaRootPerfectionStage D b
local notation "I" => Ideal.span {(p : A)}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
include hD w hw

section ModPTests
variable (N : Type u) [AddCommGroup N] [Module A N]
  [Module (A ⧸ Ideal.span {(p : A)}) N] [IsScalarTower A (A ⧸ Ideal.span {(p : A)}) N]

/-- 各実段の単位による通常テンソル写像はA/p加群上で単射。 -/
theorem deltaRootPerfectionStage_unitTensor_injective_modP (n : ℕ) :
    Function.Injective (TensorProduct.mk A (S n) N 1) := by
  let R := Q ⊗[A] S n
  have := deltaRootPerfectionStage_residueTensor_faithfullyFlat D b hD w hw n
  have hi : Function.Injective (TensorProduct.mk Q R N 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := Q) (B := R) N
  let e := ((TensorProduct.comm Q R N).restrictScalars A).trans
    ((AlgebraTensorModule.cancelBaseChange A Q Q N (S n)).restrictScalars A) |>.trans
      (TensorProduct.comm A N (S n))
  have he (x : N) : e (1 ⊗ₜ[Q] x) = (1 : S n) ⊗ₜ[A] x := by
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
      TensorProduct.comm_tmul]
    have hone : (1 : R) = ((1 : Q) ⊗ₜ[A] (1 : S n)) := rfl
    rw [hone, AlgebraTensorModule.cancelBaseChange_tmul, one_smul, TensorProduct.comm_tmul]
  intro x y h
  apply hi
  apply e.injective
  change e ((1 : R) ⊗ₜ[Q] x) = e ((1 : R) ⊗ₜ[Q] y)
  rw [he, he]
  exact h

/-- 実余極限の単位による通常テンソル写像もA/p加群上で単射。 -/
theorem deltaRootPerfection_unitTensor_injective_modP :
    Function.Injective (TensorProduct.mk A C N 1) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  change (1 : C) ⊗ₜ[A] x = 0 at hx
  let := deltaRootPerfectionLinearDirectedSystem D b
  let T := fun i j (h : i ≤ j) => (deltaRootPerfectionStageMapLE D b h).toLinearMap.rTensor N
  have hz : Module.DirectLimit.of A ℕ (fun n => S n ⊗[A] N) T 0
      ((1 : S 0) ⊗ₜ[A] x) = 0 := by
    rw [← deltaRootPerfectionTensorLimitEquiv_tmul_of D b N 0 (1 : S 0)]
    change deltaRootPerfectionTensorLimitEquiv D b N
      (deltaPerfectionOf F 0 (1 : Raw) ⊗ₜ[A] x) = 0
    rw [map_one, hx, map_zero]
  obtain ⟨m, h, hm⟩ := Module.DirectLimit.of.zero_exact hz
  change (deltaRootPerfectionStageMapLE D b h).toLinearMap.rTensor N
    ((1 : S 0) ⊗ₜ[A] x) = 0 at hm
  rw [LinearMap.rTensor_tmul] at hm
  change (deltaRootPerfectionStageMapLE D b h (1 : S 0)) ⊗ₜ[A] x = 0 at hm
  rw [map_one] at hm
  apply deltaRootPerfectionStage_unitTensor_injective_modP D b hD w hw N m
  exact hm.trans (map_zero (TensorProduct.mk A (S m) N 1)).symm

end ModPTests

/-- 実δ完全化の正確な標準剰余テンソルはA/p上忠実平坦。 -/
theorem deltaRootPerfection_residueTensor_faithfullyFlat :
    Module.FaithfullyFlat Q (Q ⊗[A] C) := by
  apply (Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality Q (Q ⊗[A] C)).mpr
  refine ⟨deltaRootPerfection_residueTensor_flat D b hD w hw, ?_⟩
  intro N _ _ hN
  let : Module A N := Module.compHom N q
  let : IsScalarTower A Q N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : Subsingleton (N ⊗[Q] (Q ⊗[A] C)) := hN
  let e := AlgebraTensorModule.cancelBaseChange A Q Q N C
  have : Subsingleton (N ⊗[A] C) := e.surjective.subsingleton
  have : Subsingleton (C ⊗[A] N) := (TensorProduct.comm A C N).injective.subsingleton
  exact (deltaRootPerfection_unitTensor_injective_modP D b hD w hw N).subsingleton

omit hD w hw in
/-- 既存の実δ完全化の完全性から、係数環のpスカラーの正則性を得る。 -/
theorem deltaRootPerfection_p_smul_regular : IsSMulRegular C (p : A) := by
  intro x y h
  apply (deltaPerfection_isPerfect F).p_mul_injective
  simp only [Algebra.smul_def, map_natCast] at h
  exact h

/-- 完全係数環の任意根族raw包の実δ完全化は、p完全忠実平坦。 -/
theorem deltaRootPerfection_isCompletelyFaithfullyFlat :
    IsCompletelyFaithfullyFlat I C :=
  isCompletelyFaithfullyFlat_principal_of_regular (p : A) hD.p_mul_injective C
    (deltaRootPerfection_p_smul_regular D b)
    (deltaRootPerfection_residueTensor_faithfullyFlat D b hD w hw)

end SerrePositivity.BhattScholze

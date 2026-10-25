module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootPerfectionModuleLimit
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatPowerTorsion

/-! # 実δ完全化の正確な標準剰余テンソルの平坦性 -/

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
local notation "C" => DeltaPerfection F
local notation "S" => DeltaRootPerfectionStage D b
local notation "I" => Ideal.span {(p : A)}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
include hD w hw

section ModPTests
variable {N N' : Type u} [AddCommGroup N] [AddCommGroup N']
  [Module A N] [Module A N']
  [Module (A ⧸ Ideal.span {(p : A)}) N] [Module (A ⧸ Ideal.span {(p : A)}) N']
  [IsScalarTower A (A ⧸ Ideal.span {(p : A)}) N]
  [IsScalarTower A (A ⧸ Ideal.span {(p : A)}) N']

/-- A/p加群の単射は、各実段との通常Aテンソルでも単射。 -/
theorem deltaRootPerfectionStage_lTensor_injective_modP
    (f : N →ₗ[A ⧸ Ideal.span {(p : A)}] N') (hf : Function.Injective f) (n : ℕ) :
    Function.Injective ((f.restrictScalars A).lTensor (S n)) := by
  let V := N' ⧸ f.range
  let fA := f.restrictScalars A
  let gA := f.range.mkQ.restrictScalars A
  have hV : ∀ a ∈ I, ∀ x : V, a • x = 0 := by
    intro a ha x
    rw [← algebraMap_smul Q a x]
    change q a • x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_smul]
  have ht := (isConcentratedInDegreeZero_derivedTensor_iff (R := A) (S n) V).mp
    ((deltaRootPerfectionStage_isCompletelyFaithfullyFlat D b hD w hw n).1 V hV) 1 (by omega)
  have he : Function.Exact fA gA := by
    change Function.Exact f f.range.mkQ
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
  exact lTensor_injective_of_torModule_one (S n) fA gA hf f.range.mkQ_surjective he ht

/-- 同じ単射性を、実段テンソル直極限を通じて実δ完全化へ移す。 -/
theorem deltaRootPerfection_lTensor_injective_modP
    (f : N →ₗ[A ⧸ Ideal.span {(p : A)}] N') (hf : Function.Injective f) :
    Function.Injective ((f.restrictScalars A).lTensor C) := by
  let g := f.restrictScalars A
  let T := fun i j (h : i ≤ j) => (deltaRootPerfectionStageMapLE D b h).toLinearMap
  let := deltaRootPerfectionLinearDirectedSystem D b
  let TN := fun i j h => (T i j h).rTensor N
  let TN' := fun i j h => (T i j h).rTensor N'
  have hc : ∀ i j h, (g.lTensor (S j)).comp (TN i j h) =
      (TN' i j h).comp (g.lTensor (S i)) := by
    intro i j h
    exact (LinearMap.lTensor_comp_rTensor (S i) (T i j h) g).trans
      (LinearMap.rTensor_comp_lTensor (S i) (T i j h) g).symm
  let t := Module.DirectLimit.map (f := TN) (f' := TN') (fun n => g.lTensor (S n)) hc
  have ht : Function.Injective t := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨n, y, rfl⟩ := Module.DirectLimit.exists_of x
    dsimp only [t] at hx
    rw [Module.DirectLimit.map_apply_of] at hx
    obtain ⟨m, h, hz⟩ := Module.DirectLimit.of.zero_exact hx
    have hz' : g.lTensor (S m) (TN n m h y) = 0 := by
      change ((g.lTensor (S m)).comp (TN n m h)) y = 0
      rw [hc]
      exact hz
    have hi := deltaRootPerfectionStage_lTensor_injective_modP D b hD w hw f hf m
    have hy : TN n m h y = 0 := hi (hz'.trans (map_zero _).symm)
    rw [← Module.DirectLimit.of_f (j := m) (hij := h), hy, map_zero]
  have hn : (deltaRootPerfectionTensorLimitEquiv D b N').toLinearMap.comp
      (g.lTensor C) = t.comp (deltaRootPerfectionTensorLimitEquiv D b N).toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    obtain ⟨n, z, rfl⟩ := Ring.DirectLimit.exists_of x
    change deltaRootPerfectionTensorLimitEquiv D b N'
      ((g.lTensor C) (deltaPerfectionOf F n z ⊗ₜ[A] y)) =
        t (deltaRootPerfectionTensorLimitEquiv D b N (deltaPerfectionOf F n z ⊗ₜ[A] y))
    rw [LinearMap.lTensor_tmul,
      deltaRootPerfectionTensorLimitEquiv_tmul_of D b N' n (ULift.up z),
      deltaRootPerfectionTensorLimitEquiv_tmul_of D b N n (ULift.up z)]
    dsimp only [t]
    rw [Module.DirectLimit.map_apply_of, LinearMap.lTensor_tmul]
  have hi : Function.Injective
      ((deltaRootPerfectionTensorLimitEquiv D b N').toLinearMap.comp (g.lTensor C)) := by
    rw [hn]
    exact ht.comp (deltaRootPerfectionTensorLimitEquiv D b N).injective
  intro x y h
  exact hi (congrArg (deltaRootPerfectionTensorLimitEquiv D b N') h)

end ModPTests

/-- 実δ完全化の通常剰余テンソルは、正確な標準係数環A/p上平坦。 -/
theorem deltaRootPerfection_residueTensor_flat : Module.Flat Q (Q ⊗[A] C) := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro N N' _ _ _ _ f hf
  let : Module A N := Module.compHom N q
  let : Module A N' := Module.compHom N' q
  let : IsScalarTower A Q N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower A Q N' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let g := f.restrictScalars A
  have hl := deltaRootPerfection_lTensor_injective_modP D b hD w hw f hf
  have hr : Function.Injective (g.rTensor C) := (g.lTensor_inj_iff_rTensor_inj C).mp hl
  let e := AlgebraTensorModule.cancelBaseChange A Q Q N C
  let e' := AlgebraTensorModule.cancelBaseChange A Q Q N' C
  have hn (x : N ⊗[Q] (Q ⊗[A] C)) :
      e' (f.rTensor (Q ⊗[A] C) x) = g.rTensor C (e x) := by
    induction x using TensorProduct.inductionOn with
    | tmul x y =>
      induction y using TensorProduct.inductionOn with
      | tmul a m => simp [e, e', AlgebraTensorModule.cancelBaseChange_tmul, g]
      | add y z hy hz => simp_all only [TensorProduct.tmul_add, map_add]
    | add x y hx hy => simp_all only [map_add]
  intro x y h
  apply e.injective
  apply hr
  rw [← hn x, ← hn y, h]

end SerrePositivity.BhattScholze

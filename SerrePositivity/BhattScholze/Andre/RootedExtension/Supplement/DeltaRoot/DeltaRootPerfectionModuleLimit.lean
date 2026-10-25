module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.DeltaRoot.DeltaRootPerfectionStageFlat
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-! # 実δ完全化とFrobenius各段のA加群直極限 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (b : σ → A)
attribute [local instance] deltaRootPerfectionStageAlgebra deltaRootPerfectionAlgebra
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "B" => DeltaAdjoinDivision E (p : P)
  (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "F" => deltaAdjoinDivisionStructure E (p : P)
  (fun s ↦ DeltaStructure.frobeniusLift E (r s))
local notation "φ" => DeltaStructure.frobeniusLift F
local notation "C" => DeltaPerfection F
local notation "S" => DeltaRootPerfectionStage D b

/-- 任意の段i≤jの実Frobenius遷移。段ごとの係数作用についてA代数射。 -/
def deltaRootPerfectionStageMapLE {i j : ℕ} (h : i ≤ j) : S i →ₐ[A] S j :=
  { (ULift.ringEquiv.symm.toRingHom).comp ((φ ^ (j-i)).comp ULift.ringEquiv.toRingHom) with
    commutes' := by
      intro a
      change ULift.up ((φ : B → B)^[j-i] ((φ : B → B)^[i]
        (deltaRootRawCoefficientMap D b a))) =
          ULift.up ((φ : B → B)^[j] (deltaRootRawCoefficientMap D b a))
      rw [← Function.iterate_add_apply]
      congr 2
      omega }

/-- 任意二段の遷移は、既存実完全化への標準射と可換。 -/
theorem deltaRootPerfectionStageAlgHom_mapLE {i j : ℕ} (h : i ≤ j) :
    (deltaRootPerfectionStageAlgHom D b j).comp (deltaRootPerfectionStageMapLE D b h) =
      deltaRootPerfectionStageAlgHom D b i := by
  ext x
  exact deltaPerfectionOf_iterate F h x.down

/-- 具体的A線形遷移の恒等・合成条件。 -/
theorem deltaRootPerfectionLinearDirectedSystem :
    DirectedSystem S (fun _ _ h => (deltaRootPerfectionStageMapLE D b h).toLinearMap) where
  map_self {i} x := by
    apply ULift.ext
    change (φ : B → B)^[i-i] x.down = x.down
    simp
  map_map {k j i} hij hjk x := by
    apply ULift.ext
    change (φ : B → B)^[k-j] ((φ : B → B)^[j-i] x.down) =
      (φ : B → B)^[k-i] x.down
    rw [← Function.iterate_add_apply]
    congr 1
    omega

/-- 実Frobenius段の、元のA上の具体的加群直極限。 -/
abbrev DeltaRootPerfectionModuleLimit :=
  Module.DirectLimit S (fun _ _ h => (deltaRootPerfectionStageMapLE D b h).toLinearMap)

/-- 各実段の標準像から、実δ完全化への標準A線形射。 -/
def deltaRootPerfectionModuleLimitMap : DeltaRootPerfectionModuleLimit D b →ₗ[A] C :=
  Module.DirectLimit.lift A ℕ S _
    (fun n => (deltaRootPerfectionStageAlgHom D b n).toLinearMap)
    (fun _ _ h x => AlgHom.congr_fun (deltaRootPerfectionStageAlgHom_mapLE D b h) x)

/-- 加群直極限の標準像は、実環直極限の元の標準像へ送られる。 -/
theorem deltaRootPerfectionModuleLimitMap_of (n : ℕ) (x : S n) :
    deltaRootPerfectionModuleLimitMap D b
      (Module.DirectLimit.of A ℕ S _ n x) = deltaPerfectionOf F n x.down := by
  rw [deltaRootPerfectionModuleLimitMap, Module.DirectLimit.lift_of]
  rfl

/-- 実環直極限のA加群と、正確な段作用を持つ加群直極限の線形同値。 -/
def deltaRootPerfectionModuleLimitEquiv : DeltaRootPerfectionModuleLimit D b ≃ₗ[A] C := by
  let := deltaRootPerfectionLinearDirectedSystem D b
  let : DirectedSystem (fun _ : ℕ => B)
      (fun i j (_ : i ≤ j) => ((φ ^ (j-i) : B →+* B) : B → B)) :=
    { map_self := by intro i x; simp
      map_map := by
        intro k j i hij hjk x
        change (φ : B → B)^[k-j] ((φ : B → B)^[j-i] x) = (φ : B → B)^[k-i] x
        rw [← Function.iterate_add_apply]
        congr 1
        omega }
  apply LinearEquiv.ofBijective (deltaRootPerfectionModuleLimitMap D b)
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨n, y, rfl⟩ := Module.DirectLimit.exists_of x
    rw [deltaRootPerfectionModuleLimitMap_of] at hx
    obtain ⟨m, h, hz⟩ := Ring.DirectLimit.of.zero_exact
      (G := fun _ : ℕ => B)
      (f' := fun (i j : ℕ) (_ : i ≤ j) => φ ^ (j-i)) (i := n) (x := y.down) hx
    have hy : deltaRootPerfectionStageMapLE D b h y = 0 := by
      apply ULift.ext
      exact hz
    rw [← Module.DirectLimit.of_f (j := m) (hij := h)]
    change Module.DirectLimit.of A ℕ S
      (fun _ _ h => (deltaRootPerfectionStageMapLE D b h).toLinearMap) m
        (deltaRootPerfectionStageMapLE D b h y) = 0
    rw [hy, map_zero]
  · intro y
    obtain ⟨n, x, rfl⟩ := Ring.DirectLimit.exists_of y
    exact ⟨Module.DirectLimit.of A ℕ S _ n (ULift.up x),
      deltaRootPerfectionModuleLimitMap_of D b n (ULift.up x)⟩

/-- 線形同値も元の全段の標準像を保つ。 -/
theorem deltaRootPerfectionModuleLimitEquiv_of (n : ℕ) (x : S n) :
    deltaRootPerfectionModuleLimitEquiv D b
      (Module.DirectLimit.of A ℕ S _ n x) = deltaPerfectionOf F n x.down :=
  deltaRootPerfectionModuleLimitMap_of D b n x

/-- 実完全化との通常テンソルは、正確な実段テンソルの直極限と同型。 -/
def deltaRootPerfectionTensorLimitEquiv (N : Type u) [AddCommGroup N] [Module A N] :
    (C ⊗[A] N) ≃ₗ[A]
      Module.DirectLimit (fun n => S n ⊗[A] N)
        (fun _ _ h => (deltaRootPerfectionStageMapLE D b h).toLinearMap.rTensor N) := by
  let := deltaRootPerfectionLinearDirectedSystem D b
  exact (TensorProduct.congr (deltaRootPerfectionModuleLimitEquiv D b).symm
    (LinearEquiv.refl A N)).trans
      (TensorProduct.directLimitLeft
        (fun _ _ h => (deltaRootPerfectionStageMapLE D b h).toLinearMap) N)

/-- 通常テンソル比較は各実段の標準純テンソルを保つ。 -/
theorem deltaRootPerfectionTensorLimitEquiv_tmul_of
    (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ) (x : S n) (y : N) :
    deltaRootPerfectionTensorLimitEquiv D b N (deltaPerfectionOf F n x.down ⊗ₜ[A] y) =
      Module.DirectLimit.of A ℕ (fun n => S n ⊗[A] N)
        (fun _ _ h => (deltaRootPerfectionStageMapLE D b h).toLinearMap.rTensor N)
        n (x ⊗ₜ[A] y) := by
  let := deltaRootPerfectionLinearDirectedSystem D b
  have he : (deltaRootPerfectionModuleLimitEquiv D b).symm
      (deltaPerfectionOf F n x.down) = Module.DirectLimit.of A ℕ S
        (fun _ _ h => (deltaRootPerfectionStageMapLE D b h).toLinearMap) n x := by
    apply (deltaRootPerfectionModuleLimitEquiv D b).injective
    rw [LinearEquiv.apply_symm_apply, deltaRootPerfectionModuleLimitEquiv_of]
  rw [deltaRootPerfectionTensorLimitEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, he, LinearEquiv.refl_apply,
    TensorProduct.directLimitLeft_tmul_of]

end SerrePositivity.BhattScholze

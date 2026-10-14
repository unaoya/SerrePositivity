module

public import SerrePositivity.IntersectionMultiplicity.DiagonalFlat
public import SerrePositivity.HomologicalAlgebra.TorTwoRingComparison
public import SerrePositivity.HomologicalAlgebra.TorFlatBaseChangeVanishing
public import SerrePositivity.HomologicalAlgebra.KoszulTorLength

/-! # 対角線への帰着：Tor と Koszul ホモロジーの比較

## 概要

`R = k[[X]]`、`S = R[[Y]]`、素イデアル `P, Q ⊆ R`、`T = S / (P S + Q^{i₂} S)` とする。
全ての `n` について

\[
\ell_R \operatorname{Tor}_n^R(R/P, R/Q) = \ell_T H_n(\delta; T).
\]

## 方針

二つの環の Tor の比較（`length_torModule_tensor_eq`）を `N = S/(δ)`、`D' = S/PS`、`D = R/P` に適用する。

- `Tor_{>0}^S(S/(δ), S/PS) = 0`：定数 `C : R → S` は平坦（定数の列 `X` は `S` の正則列）、
  `S/(δ) ≅ R` は `R` 上自由なので、平坦な係数拡大での Tor の消滅（`torModule_quotient_map_subsingleton`）。
- `S/(δ) ⊗_S S/PS ≅ S/(δ + PS) ≅ R/P`（評価 `Δ` による。`Δ ∘ i₂ = id` なので `i₂` について線形）。
- `S/PS ⊗_{R, i₂} R/Q ≅ T`、`ℓ_S Tor_n^S(S/(δ), T) = ℓ_T H_n(δ; T)`（`KoszulTorLength`）。

## 使われ方

`formalization-plans/serre-equal-characteristic.md` の K8・K9。
-/

@[expose] public noncomputable section

universe u

open IsLocalRing MvPowerSeries TensorProduct CategoryTheory

namespace SerrePositivity.DiagonalRing

variable (k : Type u) [Field k] (d : ℕ)

local notation "𝓡" => MvPowerSeries (Fin d) k

/-- 定数 `C : R → R[[Y]]` は局所準同型。 -/
instance isLocalHom_C : IsLocalHom (MvPowerSeries.C (σ := Fin d) (R := 𝓡)) := by
  constructor
  intro a ha
  have := MvPowerSeries.isUnit_iff_constantCoeff.mp ha
  simpa using this

/-- 定数 `C : R → S` は平坦。定数の列 `X` は `R[[Y]]` の上で正則列なので、局所平坦性判定法による。 -/
theorem flat_const : (const k d).Flat := by
  have hA := isWeaklyRegular_of_span_eq_maximalIdeal 𝓡 (X : Fin d → 𝓡)
    (mvPowerSeries_span_X_eq_maximalIdeal k d) (ringKrullDim_mvPowerSeries_field k d)
  -- 定数を代数構造とする
  let : Algebra 𝓡 (DiagonalRing k d) := (const k d).toAlgebra
  have : IsLocalHom (algebraMap 𝓡 (DiagonalRing k d)) := isLocalHom_C k d
  change Module.Flat 𝓡 (DiagonalRing k d)
  apply flat_of_isWeaklyRegular (B := DiagonalRing k d) (DiagonalRing k d)
    (List.ofFn X) (ofList_ofFn_X k d) hA
  rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (DiagonalRing k d)]
  exact isWeaklyRegular_mvPowerSeries_map_C (σ := Fin d) (List.ofFn X) hA

/-- `R → S/(δ)`（定数を通す）は全単射。`S/(δ) ≅ R` は評価による。 -/
theorem bijective_mk_const :
    Function.Bijective ((Ideal.Quotient.mk (diagIdeal k d)).comp (const k d)) := by
  have h : ∀ a, quotDiagEquiv k d ((Ideal.Quotient.mk (diagIdeal k d)).comp (const k d) a) = a :=
    fun a ↦ by simp
  constructor
  · intro a b hab
    rw [← h a, ← h b, hab]
  · intro y
    refine ⟨quotDiagEquiv k d y, ?_⟩
    apply (quotDiagEquiv k d).injective
    rw [h]

/-- `Tor_{>0}^S(S/(δ), S/PS) = 0`。 -/
theorem torModule_diag_coeffQuot_subsingleton (P : Ideal 𝓡) (n : ℕ) :
    Subsingleton (TorModule (DiagonalRing k d) (n + 1)
      (DiagonalRing k d ⧸ diagIdeal k d) (coeffQuot k d P)) :=
  torModule_quotient_map_subsingleton (const k d) (flat_const k d) _
    (RingHom.Flat.of_bijective (bijective_mk_const k d)) P n

section quotients

variable {A : Type u} [CommRing A]

/-- 全射 `A → M` の核が `I` なら `A/I ≅ M`。 -/
def quotEquivOfKerEq {M : Type u} [AddCommGroup M] [Module A M] (π : A →ₗ[A] M)
    (hπ : Function.Surjective π) (I : Ideal A) (h : LinearMap.ker π = I) : (A ⧸ I) ≃ₗ[A] M :=
  (Submodule.quotEquivOfEq _ _ h.symm).trans (π.quotKerEquivOfSurjective hπ)

/-- 二つの商のテンソル積：`A/I ⊗_A A/J ≅ A/(I + J)`。 -/
def tensorQuotQuotEquiv (I J : Ideal A) : ((A ⧸ I) ⊗[A] (A ⧸ J)) ≃ₗ[A] A ⧸ (I ⊔ J) := by
  let π : A →ₗ[A] (A ⧸ J) ⧸ (I • ⊤ : Submodule A (A ⧸ J)) :=
    (I • ⊤ : Submodule A (A ⧸ J)).mkQ ∘ₗ J.mkQ
  have hπ : Function.Surjective π :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker π = I ⊔ J := by
    ext f
    simp only [π, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Ideal.Quotient.mk_mem_smul_top_iff I J f
  exact (TensorProduct.quotTensorEquivQuotSMul (A ⧸ J) I).trans
    (quotEquivOfKerEq π hπ (I ⊔ J) hker).symm

end quotients

/-- 係数の商のイデアル `PS`（定数として入る）。 -/
abbrev coeffIdeal (P : Ideal 𝓡) : Ideal (DiagonalRing k d) := P.map (const k d)

/-- 評価の `R` 線形版（`R` は `i₂` で作用）。 -/
def evalL : DiagonalRing k d →ₗ[𝓡] 𝓡 where
  toFun := eval k d
  map_add' := map_add _
  map_smul' r s := by
    rw [Algebra.smul_def, map_mul, eval_algebraMap, smul_eq_mul, RingHom.id_apply]

/-- `Δ(f) ∈ P` は `f ∈ (δ) + PS` と同値。 -/
theorem eval_mem_iff (P : Ideal 𝓡) (f : DiagonalRing k d) :
    eval k d f ∈ P ↔ f ∈ diagIdeal k d ⊔ coeffIdeal k d P := by
  constructor
  · intro h
    have h1 : f - const k d (eval k d f) ∈ diagIdeal k d := by
      rw [← ker_eval, RingHom.mem_ker, map_sub, eval_const, sub_self]
    have h2 : const k d (eval k d f) ∈ coeffIdeal k d P := Ideal.mem_map_of_mem _ h
    have : f = (f - const k d (eval k d f)) + const k d (eval k d f) := by ring
    rw [this]
    exact add_mem (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
  · intro h
    have hle : diagIdeal k d ⊔ coeffIdeal k d P ≤ P.comap (eval k d) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [Ideal.mem_comap, RingHom.mem_ker.mp ((diagIdeal_le_ker k d) hx)]
        exact P.zero_mem
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simpa using ha
    exact hle h

/-- `S/((δ) + PS) ≅ R/P`（評価による。`i₂` について線形）。 -/
def quotDiagCoeffEquiv (P : Ideal 𝓡) :
    (DiagonalRing k d ⧸ (diagIdeal k d ⊔ coeffIdeal k d P)) ≃ₗ[𝓡] 𝓡 ⧸ P := by
  let π : DiagonalRing k d →ₗ[𝓡] 𝓡 ⧸ P := P.mkQ ∘ₗ evalL k d
  have hπ : Function.Surjective π :=
    (Submodule.mkQ_surjective _).comp (eval_surjective k d)
  have hker : LinearMap.ker π = (diagIdeal k d ⊔ coeffIdeal k d P).restrictScalars 𝓡 := by
    ext f
    simp only [π, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem]
    exact eval_mem_iff k d P f
  exact (Submodule.Quotient.restrictScalarsEquiv 𝓡 _).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans (π.quotKerEquivOfSurjective hπ))

/-- **`ε`**：`S/(δ) ⊗_S S/PS ≅ R/P`（`R` 線形、`R` は `i₂` で作用）。 -/
def epsEquiv (P : Ideal 𝓡) :
    ((DiagonalRing k d ⧸ diagIdeal k d) ⊗[DiagonalRing k d] coeffQuot k d P) ≃ₗ[𝓡] 𝓡 ⧸ P :=
  ((tensorQuotQuotEquiv (diagIdeal k d) (coeffIdeal k d P)).restrictScalars 𝓡).trans
    (quotDiagCoeffEquiv k d P)

/-- 変数の取り替えで入る `Q` のイデアル `Q^{i₂} S`。 -/
abbrev varIdeal (Q : Ideal 𝓡) : Ideal (DiagonalRing k d) := Q.map (algebraMap 𝓡 (DiagonalRing k d))

/-- 対角線の商 `T = S / (PS + Q^{i₂} S)`。 -/
abbrev diagonalQuot (P Q : Ideal 𝓡) : Type u :=
  DiagonalRing k d ⧸ (coeffIdeal k d P ⊔ varIdeal k d Q)

/-- `S/PS ⊗_{R, i₂} R/Q ≅ T`（`S` 線形）。 -/
def tensorCoeffQuotEquiv (P Q : Ideal 𝓡) :
    (coeffQuot k d P ⊗[𝓡] (𝓡 ⧸ Q)) ≃ₗ[DiagonalRing k d] diagonalQuot k d P Q := by
  let D' := coeffQuot k d P
  let J : Ideal D' := Q.map (algebraMap 𝓡 D')
  let e₁ : (D' ⧸ J) ≃ₗ[DiagonalRing k d] D' ⊗[𝓡] (𝓡 ⧸ Q) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot D' Q).toLinearEquiv.restrictScalars _
  let π : DiagonalRing k d →ₗ[DiagonalRing k d] D' ⧸ J := Algebra.linearMap _ _
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨y, rfl⟩
  have hJ : J = (varIdeal k d Q).map (Ideal.Quotient.mk (coeffIdeal k d P)) := by
    simp only [J, varIdeal, Ideal.map_map]
    rfl
  have hker : LinearMap.ker π = coeffIdeal k d P ⊔ varIdeal k d Q := by
    ext f
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk J (Ideal.Quotient.mk (coeffIdeal k d P) f) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, hJ, ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_comm]
  exact (e₁.symm.trans (quotEquivOfKerEq π hπ _ hker).symm)

/-- 剰余体は定数で尽くされる：`S → k` は `R` からの像で全射。 -/
theorem residue_comp_algebraMap_surjective :
    Function.Surjective ((residue (DiagonalRing k d)).comp (algebraMap 𝓡 (DiagonalRing k d))) := by
  intro y
  obtain ⟨s, rfl⟩ := residue_surjective y
  let c : k := MvPowerSeries.constantCoeff (MvPowerSeries.constantCoeff (toPS k d s))
  refine ⟨MvPowerSeries.C c, ?_⟩
  rw [RingHom.comp_apply, algebraMap_C]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq]
  -- 定数項の定数項が消えるので極大イデアルに入る
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 := MvPowerSeries.isUnit_iff_constantCoeff.mp hu
  have h2 := MvPowerSeries.isUnit_iff_constantCoeff.mp h1
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.constantCoeff
      (toPS k d (const k d (MvPowerSeries.C c) - s))) = 0 := by
    rw [show toPS k d (const k d (MvPowerSeries.C c) - s) =
      MvPowerSeries.C (MvPowerSeries.C c) - toPS k d s from rfl, map_sub, map_sub,
      MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_C, sub_self]
  change IsUnit (MvPowerSeries.constantCoeff (MvPowerSeries.constantCoeff
    (toPS k d (const k d (MvPowerSeries.C c) - s)))) at h2
  rw [h0] at h2
  exact not_isUnit_zero h2

/-- **Tor と Koszul ホモロジーの比較**：素イデアルとは限らない `P, Q` で、`T` が自明でなければ
`ℓ_R Tor_n^R(R/P, R/Q) = ℓ_T H_n(δ; T)`。 -/
theorem length_torModule_eq_length_koszulHomologySelf (P Q : Ideal 𝓡)
    (hT : coeffIdeal k d P ⊔ varIdeal k d Q ≠ ⊤) (n : ℕ) :
    Module.length 𝓡 (TorModule 𝓡 n (𝓡 ⧸ P) (𝓡 ⧸ Q)) =
      Module.length (diagonalQuot k d P Q)
        (koszulHomologySelf (algebraMap (DiagonalRing k d) (diagonalQuot k d P Q) ∘ diag k d) n) := by
  have : Nontrivial (diagonalQuot k d P Q) := Ideal.Quotient.nontrivial_iff.mpr hT
  let : IsLocalRing (diagonalQuot k d P Q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : Module.Flat 𝓡 (coeffQuot k d P) := flat_coeffQuot k d P
  have hcmp := length_torModule_tensor_eq (DiagonalRing k d ⧸ diagIdeal k d) (coeffQuot k d P)
    (epsEquiv k d P) (residue_comp_algebraMap_surjective k d)
    (torModule_diag_coeffQuot_subsingleton k d P) n (𝓡 ⧸ Q)
  rw [← hcmp]
  have hres : Function.Surjective ((residue (diagonalQuot k d P Q)).comp
      (algebraMap (DiagonalRing k d) (diagonalQuot k d P Q))) :=
    residue_surjective.comp Ideal.Quotient.mk_surjective
  have hK := isKoszulResolution_of_isWeaklyRegular (diag k d) (isWeaklyRegular_diag k d)
  rw [length_koszulHomologySelf_eq_length_torModule hres (diag k d) hK n]
  exact (((Tor (ModuleCat.{u} (DiagonalRing k d)) n).obj
    (ModuleCat.of _ (DiagonalRing k d ⧸ diagIdeal k d))).mapIso
      (tensorCoeffQuotEquiv k d P Q).toModuleIso).toLinearEquiv.length_eq

end SerrePositivity.DiagonalRing

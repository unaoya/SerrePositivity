module

public import SerrePositivity.RingTheory.Derivation
public import SerrePositivity.CommutativeAlgebra.FiniteNormalization
public import Mathlib.LinearAlgebra.Basis.SMul
public import SerrePositivity.CommutativeAlgebra.CohenGabber.CoefficientSection

/-! # Cohen–Gabber 2：微分パラメータ

概要：同標数 `p` の次元 `h` の完備 Noether 局所整域 `D` には、係数切断 `ψ` とパラメータ系 `y_1, …, y_h` で、
`D(y_i)` が生成点での完備微分 `Frac D ⊗ Ω̂_{D/k}` の基底になるものがある
（`exists_coefficient_section_differential_parameters`）。
方針：係数切断を取り替えて完備微分の次元を `h` にする（`CohenGabber/CoefficientSection`）。極大イデアル内で導分の像が
基底になる元 `f_i` を選び、元のパラメータ `τ_i` を `y_i = τ_i^p (1 + f_i)` に取り替える。`D(τ_i^p) = 0` かつ `1 + f_i`
は単元なので、`D(y_i) = τ_i^p D(f_i)` も基底で、`y` も準素。
規約：導分は完備微分の係数拡大 `baseChangeCompletedKaehlerDerivation`。
使われ方：分離性（`CohenGabber/Normalization`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

open IsLocalRing

section Selection


section Derivation
variable {R S L V : Type*} [CommRing R] [CommRing S] [IsDomain S] [IsLocalRing S]
  [Field L] [Algebra R S] [Algebra S L] [IsFractionRing S L]
  [AddCommGroup V] [Module R V] [Module S V] [Module L V]
  [IsScalarTower S L V] [FiniteDimensional L V]

/-- 非零極大イデアル内から、指定導分の像が基底となる元を選ぶ。 -/
theorem exists_basis_derivation_maximalIdeal
    (δ : Derivation R S V) (hm : maximalIdeal S ≠ ⊥)
    (hδ : Submodule.span L (Set.range δ) = ⊤)
    {h : ℕ} (hdim : Module.finrank L V = h) :
    ∃ (f : Fin h → S) (B : Module.Basis (Fin h) L V),
      (∀ i, f i ∈ maximalIdeal S) ∧ ∀ i, B i = δ (f i) := by
  obtain ⟨f, hf, hi⟩ := exists_linearIndependent_derivation_perturbation
    δ (maximalIdeal S) hm hδ (fun _ : Fin h ↦ 0) (by rw [Fintype.card_fin, hdim])
  have hi' : LinearIndependent L (fun i ↦ δ (f i)) := by
    simpa only [zero_add] using hi
  let B : Module.Basis (Fin h) L V := Module.Basis.mk hi'
    (hi'.span_eq_top_of_card_eq_finrank' (by simpa only [Fintype.card_fin] using hdim.symm)).ge
  exact ⟨f, B, hf, fun i ↦ Module.Basis.mk_apply _ _ i⟩

/-- p乗の単元倍で、同じ根基と微分基底を持つパラメータを作る。 -/
theorem exists_parameters_with_derivation_basis
    (p : ℕ) [Fact p.Prime] [CharP S p]
    (δ : Derivation R S V) (hm : maximalIdeal S ≠ ⊥)
    (hδ : Submodule.span L (Set.range δ) = ⊤)
    {h : ℕ} (hdim : Module.finrank L V = h)
    (τ : Fin h → S) (hτm : ∀ i, τ i ∈ maximalIdeal S) (hτ0 : ∀ i, τ i ≠ 0)
    (hprimary : (Ideal.span (Set.range τ)).radical = maximalIdeal S) :
    ∃ (y : Fin h → S) (B : Module.Basis (Fin h) L V),
      (∀ i, y i ∈ maximalIdeal S) ∧
      (Ideal.span (Set.range y)).radical = maximalIdeal S ∧ ∀ i, B i = δ (y i) := by
  classical
  obtain ⟨f, B, hfm, hB⟩ := exists_basis_derivation_maximalIdeal δ hm hδ hdim
  let y : Fin h → S := fun i ↦ τ i ^ p * (1 + f i)
  have hu : ∀ i, IsUnit (1 + f i) := fun i ↦ isUnit_one_add_of_mem_maximalIdeal (hfm i)
  have hyprim : (Ideal.span (Set.range y)).radical = maximalIdeal S := by
    rw [span_range_mul_units (fun i ↦ τ i ^ p) (fun i ↦ 1 + f i) hu]
    exact (radical_span_powers τ (fun _ ↦ p) (fun _ ↦ (Fact.out : p.Prime).pos)).trans hprimary
  have hδy : ∀ i, δ (y i) = algebraMap S L (τ i ^ p) • δ (f i) := by
    intro i
    simp only [y, δ.leibniz, derivation_pow_char_eq_zero p δ, smul_zero, add_zero,
      map_add, Derivation.map_one_eq_zero, zero_add]
    exact (algebraMap_smul L (τ i ^ p) (δ (f i))).symm
  have hw : ∀ i, IsUnit (algebraMap S L (τ i ^ p)) := fun i ↦
    isUnit_iff_ne_zero.mpr (by
      simpa only [map_zero] using (IsFractionRing.injective S L).ne (pow_ne_zero p (hτ0 i)))
  refine ⟨y, B.isUnitSMul hw, ?_, hyprim, ?_⟩
  · intro i
    exact (maximalIdeal S).mul_mem_right _
      ((maximalIdeal S).pow_mem_of_mem (hτm i) p (Fact.out : p.Prime).pos)
  · intro i
    rw [Module.Basis.isUnitSMul_apply, hB, hδy]
end Derivation

end Selection

universe u
open scoped TensorProduct

section CohenGabber


/-- 非零極大イデアルの完備局所整域では、係数切断と微分基底を持つパラメータを同時に選べる。 -/
theorem exists_coefficient_section_differential_parameters
    (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
    [IsAdicComplete (maximalIdeal D) D] {h : ℕ} (hdim : ringKrullDim D = h)
    (p : ℕ) [Fact p.Prime] [CharP D p] (hm : maximalIdeal D ≠ ⊥) :
    ∃ (ψ : ResidueField D →+* D) (y : Fin h → D),
      (residue D).comp ψ = RingHom.id (ResidueField D) ∧
      (∀ i, y i ∈ maximalIdeal D) ∧
      (Ideal.span (Set.range y)).radical = maximalIdeal D ∧
      letI : Algebra (ResidueField D) D := ψ.toAlgebra
      ∃ B : Module.Basis (Fin h) (FractionRing D) (FractionRing D ⊗[D]
        AdicCompletion (maximalIdeal D) (KaehlerDifferential (ResidueField D) D)),
        ∀ i, B i = baseChangeCompletedKaehlerDerivation
          (k := ResidueField D) (FractionRing D) (maximalIdeal D) (y i) := by
  classical
  let : CharP (ResidueField D) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast (residue D), CharP.cast_eq_zero, map_zero])
  obtain ⟨φ, τ, F, hφ, hτ, hF, _, _, _, hFX⟩ :=
    exists_equalCharacteristic_finite_normalization D hdim p
  have hτm : ∀ i, τ i ∈ maximalIdeal D := by
    intro i
    rw [← hτ.2]
    exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))
  obtain ⟨s, hs⟩ := exists_pBasis (K := ResidueField D) (p := p)
  obtain ⟨ψ, hψ, hdimψ⟩ := hs.exists_coefficient_section_completed_finrank
    φ hφ hdim hm τ hτm hτ.2
  let : Algebra (ResidueField D) D := ψ.toAlgebra
  have hres : Function.Surjective ((residue D).comp (algebraMap (ResidueField D) D)) := by
    change Function.Surjective ((residue D).comp ψ)
    rw [hψ]
    exact Function.surjective_id
  let : Module.Finite D (AdicCompletion (maximalIdeal D)
      (KaehlerDifferential (ResidueField D) D)) :=
    moduleFinite_completedKaehler_of_primary_common_residue hres (maximalIdeal D)
      (maximalIdeal.isMaximal D).isPrime.radical
  have hτ0 : ∀ i, τ i ≠ 0 := fun i ↦ hFX i ▸ powerSeries_variable_image_ne_zero F hF i
  obtain ⟨y, B, hym, hyprim, hB⟩ := exists_parameters_with_derivation_basis p
    (baseChangeCompletedKaehlerDerivation (k := ResidueField D)
      (FractionRing D) (maximalIdeal D)) hm
    (span_range_baseChangeCompletedKaehlerDerivation_eq_top
      (FractionRing D) (maximalIdeal D) (maximalIdeal_le_jacobson ⊥))
    hdimψ τ hτm hτ0 hτ.2
  exact ⟨ψ, y, hψ, hym, hyprim, B, hB⟩

end CohenGabber

end SerrePositivity

module

public import SerrePositivity.CommutativeAlgebra.DerivationIdealSpan
public import SerrePositivity.CommutativeAlgebra.FinitePowerSeriesNormalization
public import SerrePositivity.CommutativeAlgebra.DerivationSpan
public import Mathlib.LinearAlgebra.Basis.SMul

/-! # 微分基底を持つパラメータの選択

極大イデアル内の微分基底から、既存パラメータのp乗の単元倍を構成する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open IsLocalRing

/-- 各生成元の単元倍は、同じイデアルを生成する。 -/
theorem span_range_mul_units {S ι : Type*} [CommRing S]
    (z u : ι → S) (hu : ∀ i, IsUnit (u i)) :
    Ideal.span (Set.range (fun i ↦ z i * u i)) = Ideal.span (Set.range z) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨v, hv⟩ := hu i
    have h := Ideal.mul_mem_right (↑v⁻¹)
      (Ideal.span (Set.range (fun i ↦ z i * u i)))
      (Ideal.subset_span (Set.mem_range_self i))
    change z i ∈ Ideal.span (Set.range (fun i ↦ z i * u i))
    simpa only [← hv, mul_assoc, Units.val_mul, Units.mul_inv, Units.val_one, mul_one] using h

/-- 極大イデアル内の元を1に加えると単元となる。 -/
theorem isUnit_one_add_of_mem_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S]
    {f : S} (hf : f ∈ maximalIdeal S) : IsUnit (1 + f) := by
  apply notMem_maximalIdeal.mp
  intro h
  have h1 : (1 : S) ∈ maximalIdeal S := by
    simpa only [add_sub_cancel_right] using (maximalIdeal S).sub_mem h hf
  exact (maximalIdeal.isMaximal S).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

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
    δ (maximalIdeal S) hm hδ (fun _ : Fin h ↦ 0) (by rw [hdim])
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

end SerrePositivity

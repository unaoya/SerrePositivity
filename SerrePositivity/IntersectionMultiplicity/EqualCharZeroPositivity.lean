module

public import SerrePositivity.IntersectionMultiplicity.DiagonalPositivity
public import SerrePositivity.IntersectionMultiplicity.Devissage
public import SerrePositivity.IntersectionMultiplicity.BaseChange
public import SerrePositivity.CommutativeAlgebra.CharZeroCoefficientField
public import SerrePositivity.CommutativeAlgebra.AdicCompletionNoetherian
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! # 剰余標数零の正則局所環での Serre の正値性

## 概要

剰余体が標数零の正則局所環 `R` と有限生成加群 `M, N` について、`M ⊗ N` が有限長で
`dim M + dim N = dim R` なら `χ^R(M, N) > 0`。

## 方針

1. **完備化**：平坦な完備化は長さ・次元・正則性・`χ` を保つ。
2. **Cohen 同型**：完備なら標数零の係数体 `k → R` があり（`exists_residue_section_of_charZero`）、
   正則パラメータ系への評価 `k[[X_1, …, X_d]] → R` は全射で、両辺の次元が等しいので単射。
3. **冪級数環へ移す**：環同型は平坦で極大イデアルを保つので `χ` を保つ。
4. **素イデアル商**：デヴィサージュ（`chi_pos_of_prime_quotients`）と、冪級数環での
   対角線論法（`DiagonalRing.chi_pos_of_prime`）。

デヴィサージュは交点重複度の消滅定理（`Inputs.intersectionVanishing`）を使う。

## 使われ方

`Paper/Section5/CharacteristicZeroReduction` の `positivity_of_residueCharZero` を、
Serre の等標数正値性の一般形の引用（旧 `Inputs.serrePositivity_of_field`、削除済み）なしで示すのに使う（計画 K11）。
-/

@[expose] public noncomputable section

universe u

open IsLocalRing TensorProduct

namespace SerrePositivity

/-- **Cohen 同型（標数零）**：剰余体が標数零の完備正則局所環 `R` は、剰余体上の冪級数環と同型。 -/
theorem exists_mvPowerSeries_ringEquiv_of_charZero (R : Type u) [CommRing R]
    [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)] :
    ∃ (K : Type u) (_ : Field K) (d : ℕ), Nonempty (MvPowerSeries (Fin d) K ≃+* R) := by
  classical
  obtain ⟨g, hg⟩ := exists_residue_section_of_charZero R
  obtain ⟨d, x, hrange, _, hdim⟩ := exists_regular_generators_fin R
  have hx : ∀ i, x i ∈ maximalIdeal R := fun i ↦ hrange ▸ Ideal.subset_span ⟨i, rfl⟩
  let c := adicPowerSeriesEval g (maximalIdeal R) x hx
  have hsurj : Function.Surjective c := by
    apply adicPowerSeriesEval_surjective g (maximalIdeal R) x hx hrange
    intro a
    exact ⟨a, RingHom.congr_fun hg a⟩
  let := isRegularLocalRing_mvPowerSeries_fin (ResidueField R) d
  let : IsDomain (MvPowerSeries (Fin d) (ResidueField R)) := isDomain_of_isRegularLocalRing _
  have hinj : Function.Injective c := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hf0
    have hdrop := ringKrullDim_succ_le_of_surjective c hsurj
      (mem_nonZeroDivisors_iff_ne_zero.mpr hf0) hf
    rw [ringKrullDim_mvPowerSeries_field, hdim] at hdrop
    have : (d : WithBot ℕ∞) + 1 ≤ d := hdrop
    have h' : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : ℕ) := by exact_mod_cast this
    have := WithBot.coe_le_coe.mp h'
    norm_cast at this
    omega
  exact ⟨ResidueField R, inferInstance, d, ⟨RingEquiv.ofBijective c ⟨hinj, hsurj⟩⟩⟩

/-- 完備な剰余標数零の正則局所環での正値性。 -/
theorem chi_pos_of_complete_residueCharZero (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  obtain ⟨k, _, d, ⟨e⟩⟩ := exists_mvPowerSeries_ringEquiv_of_charZero R
  let B := MvPowerSeries (Fin d) k
  let : Algebra R B := e.symm.toRingHom.toAlgebra
  have : Module.Flat R B :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_bijective e.symm.bijective)
  have hm : (maximalIdeal R).map (algebraMap R B) = maximalIdeal B :=
    map_ringEquiv_maximalIdeal e.symm
  rw [← chi_baseChange_of_map_maximalIdeal R B hm M N]
  apply chi_pos_of_prime_quotients (DiagonalRing.chi_pos_of_prime k d) (B ⊗[R] M) (B ⊗[R] N)
  · rwa [tensorLength_baseChange_of_map_maximalIdeal R B hm M N]
  · rwa [supportDim_baseChange_of_map_maximalIdeal R B hm M,
      supportDim_baseChange_of_map_maximalIdeal R B hm N,
      ringKrullDim_eq_of_flat_of_map_maximalIdeal R B hm]

/-- **剰余標数零の Serre の正値性**：剰余体が標数零の正則局所環 `R` と有限生成加群 `M, N` について、
`M ⊗ N` が有限長で `dim M + dim N = dim R` なら `χ^R(M, N) > 0`。完備化で完備な場合に帰着する。 -/
theorem chi_pos_of_residueCharZero (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [CharZero (ResidueField R)]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  let S := AdicCompletion (maximalIdeal R) R
  let : IsNoetherianRing S := isNoetherianRing_adicCompletion R (maximalIdeal R)
  have hm : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    AdicCompletion.maximalIdeal_eq_map.symm
  let : IsRegularLocalRing S := isRegularLocalRing_of_flat_of_map_maximalIdeal R S hm
  let : CharZero (ResidueField S) := charZero_of_injective_ringHom
    (f := ResidueField.map (algebraMap R S)) (RingHom.injective _)
  rw [← chi_baseChange_of_map_maximalIdeal R S hm M N]
  apply chi_pos_of_complete_residueCharZero S (S ⊗[R] M) (S ⊗[R] N)
  · rwa [tensorLength_baseChange_of_map_maximalIdeal R S hm M N]
  · rwa [supportDim_baseChange_of_map_maximalIdeal R S hm M,
      supportDim_baseChange_of_map_maximalIdeal R S hm N,
      ringKrullDim_eq_of_flat_of_map_maximalIdeal R S hm]

end SerrePositivity

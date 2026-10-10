module

public import SerrePositivity.LengthAlgebra.Koszul
public import SerrePositivity.IntersectionMultiplicity.NormalizedTor
public import SerrePositivity.CommutativeAlgebra.RegularSequenceLength

/-! # λ-平坦性から共通 Euler 理論への入力

λ-平坦性は有限長加群の正次数 Tor の長さ零として個別の引数で受け取る。
剰余体での判定には有限ランクを要求しない。有限ランクを加えると、
正則パラメータの全ての正の冪について Koszul 有限性・消滅・商の長さが従う。
正則列であることは明示的な入力で、正則局所環に関する未証明の引用を使わない。
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.LengthAlgebra

open IsLocalRing
open scoped ENNReal

variable {A C : Type u} [CommRing A] [IsLocalRing A] [CommRing C]
  (φ : A →+* C) (lam : NormalizedLength C ((maximalIdeal A).map φ))
  {e : ℕ} (z : Fin e → A) (hz : Ideal.span (Set.range z) = maximalIdeal A)

include hz in
/-- 剰余体の Koszul 分解により、λ-平坦性を一つの列で判定する。 -/
theorem flat_iff_koszul (hK : IsKoszulResolution z) :
    (∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
      ∀ i : ℕ, 0 < i → lam.len (TorAlg φ i V) = 0) ↔
    (∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (φ ∘ z) i) = 0) := by
  rw [normalizedLength_tor_pos_eq_zero_iff_residue]
  apply forall_congr'
  intro i
  rw [lam.len_congr _ _ ((torAlgCongr φ i (Submodule.quotEquivOfEq _ _ hz.symm)).trans
    (torAlgKoszulEquiv φ z hK i))]

include hz in
/-- 一つの Koszul 列の消滅と有限な零次の値から、全有限長加群の Tor を計算する。 -/
theorem tor_length_of_koszul (hK : IsKoszulResolution z)
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (φ ∘ z) i) = 0)
    (r : ℝ≥0∞) (hr : r ≠ ⊤)
    (hquot : lam.len (C ⧸ Ideal.span (Set.range (φ ∘ z))) = r)
    (V : Type u) [AddCommGroup V] [Module A V] (hV : IsFiniteLength A V) :
    (∀ i : ℕ, 0 < i → lam.len (TorAlg φ i V) = 0) ∧
      lam.len (TorAlg φ 0 V) = r * ENat.toENNReal (Module.length A V) ∧
      (∀ i : ℕ, lam.len (TorAlg φ i V) ≠ ⊤) := by
  have hk (i : ℕ) := lam.len_congr _ _
    ((torAlgCongr φ i (Submodule.quotEquivOfEq _ _ hz.symm)).trans (torAlgKoszulEquiv φ z hK i))
  apply normalizedLength_tor_of_residue φ lam r hr
  · intro i hi
    rw [hk i]
    exact hzero i hi
  · rw [hk 0]
    change lam.len ((koszulComplex (φ ∘ z)).homology 0) = r
    rw [lam.len_congr _ _ (koszulComplex_homology_zero_equiv (φ ∘ z)).some]
    exact hquot
  · exact hV

include hz in
/-- 座標によらない λ-平坦性・テンソル積のランク条件と、一乗の Koszul 条件は同値。 -/
theorem flat_rank_iff_koszul (hK : IsKoszulResolution z) (r : ℝ≥0∞) (hr : r ≠ ⊤) :
    ((∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
      ∀ i : ℕ, 0 < i → lam.len (TorAlg φ i V) = 0) ∧
      (∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
        lam.len ((ModuleCat.extendScalars φ).obj (ModuleCat.of A V)) =
          r * ENat.toENNReal (Module.length A V))) ↔
    ((∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (φ ∘ z) i) = 0) ∧
      lam.len (C ⧸ Ideal.span (Set.range (φ ∘ z))) = r) := by
  have hk0 : lam.len (TorAlg φ 0 (A ⧸ maximalIdeal A)) =
      lam.len (C ⧸ Ideal.span (Set.range (φ ∘ z))) := by
    exact lam.len_congr _ _
      (((torAlgCongr φ 0 (Submodule.quotEquivOfEq _ _ hz.symm)).trans
        (torAlgKoszulEquiv φ z hK 0)).trans (koszulComplex_homology_zero_equiv (φ ∘ z)).some)
  constructor
  · rintro ⟨hflat, hrank⟩
    refine ⟨(flat_iff_koszul φ lam z hz hK).mp hflat, ?_⟩
    rw [← hk0, normalizedLength_tor_zero_eq_tensor]
    exact (normalizedLength_tensor_rank_iff_residue φ lam hflat r hr).mp hrank
  · rintro ⟨hzero, hquot⟩
    have hflat := (flat_iff_koszul φ lam z hz hK).mpr hzero
    refine ⟨hflat, (normalizedLength_tensor_rank_iff_residue φ lam hflat r hr).mpr ?_⟩
    rw [← normalizedLength_tor_zero_eq_tensor, hk0, hquot]

variable [IsNoetherianRing A]

/-- 基底の極大イデアルの像は有限生成。評価先の環に Noether 性は不要。 -/
lemma parameterIdeal_fg : ((maximalIdeal A).map φ).FG :=
  (maximalIdeal A).fg_of_isNoetherianRing.map φ

include hz in
omit [IsNoetherianRing A] in
/-- 極大イデアルの像は基底パラメータの像で支持される。 -/
lemma parameterIdeal_support :
    (maximalIdeal A).map φ ≤ (Ideal.span (Set.range (φ ∘ z))).radical := by
  rw [← hz, Ideal.map_span, ← Set.range_comp]
  exact Ideal.le_radical

variable (hreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z))
  (hflat : ∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
    ∀ i : ℕ, 0 < i → lam.len (TorAlg φ i V) = 0)

include hz hreg in
/-- 正則パラメータの冪で割った商は有限長。 -/
lemma parameter_powers_finiteLength (v : ℕ) (hv : 0 < v) :
    IsFiniteLength A (A ⧸ Ideal.span (Set.range fun j ↦ z j ^ v)) := by
  apply Module.length_ne_top_iff.mp
  rw [length_quotient_parameter_powers z hz hreg v hv]
  exact WithTop.pow_ne_top (ENat.natCast_ne_top v)

include hz hreg hflat in
/-- λ-平坦性は全ての正の冪での Koszul 消滅を与える。有限ランクは不要。 -/
theorem koszulAcyclic_of_flat : KoszulAcyclic lam (φ ∘ z) := by
  intro v hv i hi
  have h := hflat _ (parameter_powers_finiteLength z hz hreg v hv) i hi
  rw [lam.len_congr _ _ (torAlgKoszulEquiv φ _
    (isKoszulResolution_powers_of_isWeaklyRegular z hz hreg v hv) i)] at h
  rw [show φ ∘ (fun j ↦ z j ^ v) = (fun j ↦ φ (z j) ^ v) from
    funext fun j ↦ map_pow φ (z j) v] at h
  exact h

variable (r : ℝ≥0∞) (hr : r ≠ ⊤)
  (hrank : lam.len (TorAlg φ 0 (A ⧸ maximalIdeal A)) = r)

include hz hreg hflat hr hrank in
/-- 有限な剰余体での値から、全てのパラメータ冪の商の長さを得る。 -/
theorem quotient_length_powers_of_flat (v : ℕ) (hv : 0 < v) :
    lam.len (C ⧸ Ideal.span (Set.range fun j ↦ φ (z j) ^ v)) = (v : ℝ≥0∞) ^ e * r := by
  have hk := (normalizedLength_tor_pos_eq_zero_iff_residue φ lam).mp hflat
  have h := (normalizedLength_tor_of_residue φ lam r hr hk hrank _
    (parameter_powers_finiteLength z hz hreg v hv)).2.1
  rw [lam.len_congr _ _ (torAlgKoszulEquiv φ _
    (isKoszulResolution_powers_of_isWeaklyRegular z hz hreg v hv) 0)] at h
  change lam.len ((koszulComplex (φ ∘ (fun j ↦ z j ^ v))).homology 0) = _ at h
  rw [lam.len_congr _ _ (koszulComplex_homology_zero_equiv (φ ∘ (fun j ↦ z j ^ v))).some,
    length_quotient_parameter_powers z hz hreg v hv] at h
  rw [show φ ∘ (fun j ↦ z j ^ v) = (fun j ↦ φ (z j) ^ v) from
    funext fun j ↦ map_pow φ (z j) v] at h
  simpa [mul_comm r] using h

include hz hreg hflat hr hrank in
/-- λ-平坦性と有限ランクから、共通 Euler 理論が必要とする Koszul 有限性を供給する。 -/
theorem koszulFinite_of_flat : KoszulFinite lam (φ ∘ z) := by
  intro v hv q
  apply koszul_finite_of_zero_positive lam (fun j ↦ φ (z j) ^ v)
    (koszulAcyclic_of_flat φ lam z hz hreg hflat v hv)
  rw [quotient_length_powers_of_flat φ lam z hz hreg hflat r hr hrank v hv]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top v)) hr

include hz hreg hflat hr hrank in
/-- λ-平坦な有限ランクの代数の Koszul Euler 数はそのランク。 -/
theorem koszulEuler_of_flat : koszulEuler lam (φ ∘ z) = r.toReal := by
  rw [koszulEuler_eq_length_quotient lam _
    ((flat_iff_koszul φ lam z hz (isKoszulResolution_of_isWeaklyRegular z hreg)).mp hflat)]
  have h := quotient_length_powers_of_flat φ lam z hz hreg hflat r hr hrank 1 one_pos
  rw [show (fun j ↦ φ (z j) ^ 1) = φ ∘ z from funext fun j ↦ pow_one _] at h
  simpa only [Nat.cast_one, one_pow, one_mul] using congrArg ENNReal.toReal h

end SerrePositivity.LengthAlgebra

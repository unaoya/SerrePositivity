module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomologicalAlgebra.TorLES
public import SerrePositivity.HomologicalAlgebra.TorFiniteLength
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.LengthAlgebra.Core
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Topology.Instances.ENNReal.ENatENNReal
public import SerrePositivity.LengthAlgebra.Koszul
public import SerrePositivity.CommutativeAlgebra.Length.QuotientPower
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite

/-! # λ-平坦性・λ-CM 性と Tor の正規化長さ

## 概要

λ-平坦性（有限長加群の正次数 Tor の長さ零）と λ-CM 性を個別の引数で受け取り、正則パラメータの冪について Koszul 有限性・消滅・商の長さを導く。有限な単射 A → D では A のパラメータ系を D に移せる。極大イデアルを生成する弱正則列について、有限長加群の Tor の正規化長さを計算する（`normalizedLength_tor_of_isWeaklyRegular`、Corollary 2.6 と Lemma 3.4 の共通部分）。

## 方針

Tor は Koszul 分解で計算し、正規化長さの加法性と Koszul ホモロジーの評価から各次数を求める。

## 規約

正則列であることは明示的な入力で、正則局所環の未証明の引用は使わない（refactor-plan §5.2 の 5 により IntersectionMultiplicity/NormalizedTor を合わせた）。

## 使われ方

Paper の Corollary 2.6・Lemma 3.4・§5、IntersectionMultiplicity/ParameterQuotient。
-/

@[expose] public noncomputable section

universe u

section NormalizedTorPart

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

variable [IsLocalRing A]

/-- λ-平坦性は剰余体だけで判定できる。零次の長さの有限性は不要。 -/
theorem normalizedLength_tor_pos_eq_zero_iff_residue
    (lam : NormalizedLength C ((maximalIdeal A).map φ)) :
    (∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
      ∀ i : ℕ, 0 < i → lam.len (TorAlg φ i V) = 0) ↔
    (∀ i : ℕ, 0 < i → lam.len (TorAlg φ i (A ⧸ maximalIdeal A)) = 0) := by
  constructor
  · intro h
    have : IsSimpleModule A (A ⧸ maximalIdeal A) := by
      rw [isSimpleModule_iff_isCoatom]
      exact Ideal.isMaximal_def.mp (maximalIdeal.isMaximal A)
    exact h _ (isFiniteLength_of_isSimpleModule (A ⧸ maximalIdeal A))
  · intro hk V _ _ hV
    induction hV with
    | @of_subsingleton V _ _ _ =>
      intro i _
      have := torAlg_subsingleton φ i V
      exact lam.len_eq_zero_of_subsingleton _
    | @of_simple_quotient V _ _ N _ hN ih =>
      have hVfl : IsFiniteLength A V := IsFiniteLength.of_simple_quotient hN
      have hQfl : IsFiniteLength A (V ⧸ N) := isFiniteLength_of_isSimpleModule (V ⧸ N)
      obtain ⟨eQ⟩ := IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal
        (A := A) (M := V ⧸ N)
      obtain ⟨α, β, δ, h₁, h₂, h₃, hβ⟩ := torAlg_longExact φ N.subtype N.mkQ
        N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
      intro i hi
      exact lam.len_eq_zero_of_exact (α i) (β i) (h₁ i)
        (torAlg_isPowTorsion φ i N hN) (torAlg_isPowTorsion φ i V hVfl)
        (torAlg_isPowTorsion φ i (V ⧸ N) hQfl) (ih i hi)
        (by rw [lam.len_congr _ _ (torAlgCongr φ i eQ)]; exact hk i hi)

/-- 剰余体での正次数の長さ零と零次の値から、有限長加群の Tor の長さを計算する。
基底の正則性や Koszul 分解は不要で、係数 `r` は任意の有限な非負実数でよい。 -/
theorem normalizedLength_tor_of_residue
    (lam : NormalizedLength C ((maximalIdeal A).map φ)) (r : ℝ≥0∞) (hr : r ≠ ⊤)
    (hkpos : ∀ i : ℕ, 0 < i → lam.len (TorAlg φ i (A ⧸ maximalIdeal A)) = 0)
    (hk0 : lam.len (TorAlg φ 0 (A ⧸ maximalIdeal A)) = r)
    (V : Type u) [AddCommGroup V] [Module A V] (hV : IsFiniteLength A V) :
    (∀ i : ℕ, 0 < i → lam.len (TorAlg φ i V) = 0) ∧
      lam.len (TorAlg φ 0 V) = r * ENat.toENNReal (Module.length A V) ∧
      (∀ i : ℕ, lam.len (TorAlg φ i V) ≠ ⊤) := by
  have hkfin : ∀ i : ℕ, lam.len (TorAlg φ i (A ⧸ maximalIdeal A)) ≠ ⊤ := by
    intro i
    rcases i with _ | i
    · rwa [hk0]
    · rw [hkpos (i + 1) (by omega)]; exact ENNReal.zero_ne_top
  induction hV with
  | @of_subsingleton V _ _ _ =>
    have h0 : ∀ i, lam.len (TorAlg φ i V) = 0 := fun i ↦
      have := torAlg_subsingleton φ i V
      lam.len_eq_zero_of_subsingleton _
    refine ⟨fun i _ ↦ h0 i, ?_, fun i ↦ by rw [h0 i]; exact ENNReal.zero_ne_top⟩
    rw [h0 0, Module.length_eq_zero_iff.mpr ‹Subsingleton V›]
    simp
  | @of_simple_quotient V _ _ N _ hN ih =>
    obtain ⟨ihpos, ih0, ihfin⟩ := ih
    have hVfl : IsFiniteLength A V := IsFiniteLength.of_simple_quotient hN
    have hQfl : IsFiniteLength A (V ⧸ N) := isFiniteLength_of_isSimpleModule (V ⧸ N)
    obtain ⟨eQ⟩ := IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := A) (M := V ⧸ N)
    have hQ : ∀ i, lam.len (TorAlg φ i (V ⧸ N)) = lam.len (TorAlg φ i (A ⧸ maximalIdeal A)) :=
      fun i ↦ lam.len_congr _ _ (torAlgCongr φ i eQ)
    obtain ⟨α, β, δ, h₁, h₂, h₃, hβ⟩ := torAlg_longExact φ N.subtype N.mkQ N.injective_subtype
      N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
    have tN := fun i ↦ torAlg_isPowTorsion φ i N hN
    have tV := fun i ↦ torAlg_isPowTorsion φ i V hVfl
    have tQ := fun i ↦ torAlg_isPowTorsion φ i (V ⧸ N) hQfl
    have hpos : ∀ i : ℕ, 0 < i → lam.len (TorAlg φ i V) = 0 := fun i hi ↦
      lam.len_eq_zero_of_exact (α i) (β i) (h₁ i) (tN i) (tV i) (tQ i) (ihpos i hi)
        (by rw [hQ i]; exact hkpos i hi)
    refine ⟨hpos, ?_, fun i ↦ ?_⟩
    · -- 0 次：`len (Tor_0 V) = len (Tor_0 N) + len (Tor_0 k)`
      have hker : lam.len (LinearMap.ker (α 0)) = 0 := by
        rw [LinearMap.exact_iff.mp (h₃ 0)]
        exact lam.len_range_eq_zero (δ 0) (tQ 1) (by rw [hQ 1]; exact hkpos 1 one_pos)
      rw [lam.len_eq_add_of_exact_of_surjective (α 0) (β 0) (h₁ 0) hβ (tN 0) (tV 0) hker, ih0,
        hQ 0, hk0, Module.length_eq_succ_of_isSimpleModule_quotient N, ENat.toENNReal_add,
        ENat.toENNReal_one, mul_add, mul_one]
    · rcases i with _ | i
      · exact lam.len_ne_top_of_exact (α 0) (β 0) (h₁ 0) (tN 0) (tV 0) (tQ 0) (ihfin 0)
          (by rw [hQ 0]; exact hkfin 0)
      · rw [hpos (i + 1) (by omega)]; exact ENNReal.zero_ne_top

/-- **有限長加群の `Tor` の正規化長さ**：`z` が `m_A` を生成する弱正則列で、Koszul ホモロジーの評価
`h39a`（`λ(H_i(φ z; C)) = 0 (i > 0)`）と `h39b`（`λ(C/(φ z)C) = r`）が成り立つなら、有限長 `A` 加群
`V` について `λ(Tor_i^A(C, V)) = 0 (i > 0)`、`λ(Tor_0^A(C, V)) = r · ℓ_A(V)`、すべて有限。
組成列についての帰納法で、`V = k` の場合は Koszul 分解、一般の場合は `Tor` の長完全列による
（モジュール docstring 参照）。 -/
theorem normalizedLength_tor_of_isWeaklyRegular {e : ℕ} (z : Fin e → A)
    (hz : Ideal.span (Set.range z) = maximalIdeal A)
    (hreg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z))
    (lam : NormalizedLength C ((maximalIdeal A).map φ)) (r : ℕ)
    (h39a : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (φ ∘ z) i) = 0)
    (h39b : lam.len (C ⧸ Ideal.span (Set.range (φ ∘ z))) = r)
    (V : Type u) [AddCommGroup V] [Module A V] (hV : IsFiniteLength A V) :
    (∀ i : ℕ, 0 < i → lam.len (TorAlg φ i V) = 0) ∧
      lam.len (TorAlg φ 0 V) = (r : ℝ≥0∞) * ENat.toENNReal (Module.length A V) ∧
      (∀ i : ℕ, lam.len (TorAlg φ i V) ≠ ⊤) := by
  -- `k = A/m` の場合の値
  have hK : IsKoszulResolution z := isKoszulResolution_of_isWeaklyRegular z hreg
  have hk : ∀ i : ℕ, lam.len (TorAlg φ i (A ⧸ maximalIdeal A)) =
      lam.len (koszulHomologySelf (φ ∘ z) i) := by
    intro i
    exact lam.len_congr _ _
      ((torAlgCongr φ i (Submodule.quotEquivOfEq _ _ hz.symm)).trans (torAlgKoszulEquiv φ z hK i))
  have hk0 : lam.len (TorAlg φ 0 (A ⧸ maximalIdeal A)) = r := by
    rw [hk 0, ← h39b]
    exact lam.len_congr _ _ (koszulComplex_homology_zero_equiv (φ ∘ z)).some
  have hkpos : ∀ i : ℕ, 0 < i → lam.len (TorAlg φ i (A ⧸ maximalIdeal A)) = 0 := by
    intro i hi
    rw [hk i]
    exact h39a i hi
  exact normalizedLength_tor_of_residue φ lam r (ENNReal.natCast_ne_top r) hkpos hk0 V hV

end SerrePositivity

end NormalizedTorPart

section FlatPart

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

end FlatPart

section CohenMacaulayPart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.LengthAlgebra

open IsLocalRing

variable {D C : Type u} [CommRing D] [IsLocalRing D] [CommRing C]
  (ψ : D →+* C) {J : Ideal C} (lam : NormalizedLength C J)
  (hzero : ∀ {h : ℕ} (x : Fin h → D), IsSystemOfParameters D x →
    ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (ψ ∘ x) i) = 0)
  (hfinite : ∀ {h : ℕ} (x : Fin h → D), IsSystemOfParameters D x →
    lam.len (C ⧸ Ideal.span (Set.range (ψ ∘ x))) ≠ ⊤)
  {h : ℕ} (x : Fin h → D) (hx : IsSystemOfParameters D x)

include hzero hx in
/-- λ-CM 消滅から、一つのパラメータ系の全ての正の冪での消滅を得る。 -/
theorem koszulAcyclic_of_cm : KoszulAcyclic lam (ψ ∘ x) := by
  intro v hv i hi
  have hh := hzero (fun j ↦ x j ^ v) (IsSystemOfParameters.pow D hx v hv) i hi
  rw [show ψ ∘ (fun j ↦ x j ^ v) = (fun j ↦ ψ (x j) ^ v) from
    funext fun j ↦ map_pow ψ (x j) v] at hh
  exact hh

section base

variable {A : Type u} [CommRing A] [IsLocalRing A] [Algebra A D] [Module.Finite A D]
  [Algebra A C] [Algebra D C] [IsScalarTower A D C]
  (hinj : Function.Injective (algebraMap A D))
  (nu : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
  (hcm : ∀ {h : ℕ} (x : Fin h → D), IsSystemOfParameters D x →
    ∀ i : ℕ, 0 < i → nu.len (koszulHomologySelf (algebraMap D C ∘ x) i) = 0)
  (hcmfin : ∀ {h : ℕ} (x : Fin h → D), IsSystemOfParameters D x →
    nu.len (C ⧸ Ideal.span (Set.range (algebraMap D C ∘ x))) ≠ ⊤)
  {e : ℕ} (z : Fin e → A) (hz : Ideal.span (Set.range z) = maximalIdeal A)
  (hdim : ringKrullDim A = e) (hK : IsKoszulResolution z)

end base

end SerrePositivity.LengthAlgebra

end CohenMacaulayPart

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Paper "Eq (3.10)"] _root_.SerrePositivity.normalizedLength_tor_of_isWeaklyRegular
attribute [cite Paper "Lemma 3.4"] _root_.SerrePositivity.normalizedLength_tor_of_isWeaklyRegular
attribute [cite Paper "Lemma 4.4"] _root_.SerrePositivity.normalizedLength_tor_of_isWeaklyRegular

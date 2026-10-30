module

public import SerrePositivity.HomologicalAlgebra.TorLES
public import SerrePositivity.HomologicalAlgebra.TorFiniteLength
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.PerfectComplex.NormalizedLength
public import SerrePositivity.CommutativeAlgebra.KoszulResolution
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Topology.Instances.ENNReal.ENatENNReal

/-!
# 有限長加群の `Tor` の正規化長さ

## 概要

Corollary 2.6 と Lemma 3.4 に共通する一般定理 `normalizedLength_tor_of_isWeaklyRegular`。仮定は

- `A` は局所環で、`z` は極大イデアル `m_A` を生成する弱正則列、
- `C` は `A` 代数（`φ : A →+* C`）、
- `λ` は `m_A C` の冪で消える `C` 加群の上で加法的な正規化長さ、
- Koszul ホモロジーの評価（論文 (3.9)）：`λ(H_i(φ z; C)) = 0 (i > 0)`、`λ(C/(φ z)C) = r`。

結論は、有限長 `A` 加群 `V` に対する公式 `λ(Tor_i^A(C, V)) = 0 (i > 0)`、
`λ(Tor_0^A(C, V)) = r · ℓ_A(V)`、そしてすべての `λ(Tor_i^A(C, V))` が有限。Corollary 2.6
（`Paper/Corollary2_6.lean`）と Lemma 3.4（`Paper/Lemma3_4.lean`）は、これを長さ代数の性質
（Theorem 2.5 の (2.4)、(2.6)）から得た `(C, λ, r)` に適用したものである。

## 証明

組成列についての帰納法（`IsFiniteLength` の帰納原理）。`V = k = A/m_A` では、Koszul 分解により
`Tor_i^A(C, k) ≅ H_i(φ z; C)`（`CommutativeAlgebra/KoszulResolution.lean` の `torAlgKoszulEquiv`）
なので仮定そのもの。一般には短完全列 `0 → N → V → V/N → 0`（`V/N` は単純、したがって `≅ k`）の
`Tor` 長完全列（`HomologicalAlgebra/TorLES.lean` の `torAlg_longExact`）を使う：

- 正次数では両端が `0` なので中央も `0`（`len_eq_zero_of_exact`）。
- `0` 次では `Tor_1(C, k) = 0` から `Tor_0(C, N) → Tor_0(C, V) → Tor_0(C, k) → 0` の最初の射の核が
  長さ `0` で、`λ` が加法的（`len_eq_add_of_exact_of_surjective`）、`ℓ_A(V) = ℓ_A(N) + 1`。
- 有限性は両端の有限性から（`len_ne_top_of_exact`）。

`Tor` が `m_A C` 冪ねじれであること（`CommutativeAlgebra/TorFiniteLength.lean`）で、各項が `λ` の
加法性の対象になる。
-/

@[expose] public section

universe u

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

/-- 零次 Tor と通常の係数拡大（テンソル積）は同じ長さをもつ。 -/
theorem normalizedLength_tor_zero_eq_tensor
    (lam : NormalizedLength C ((maximalIdeal A).map φ))
    (V : Type u) [AddCommGroup V] [Module A V] :
    lam.len (TorAlg φ 0 V) =
      lam.len ((ModuleCat.extendScalars φ).obj (ModuleCat.of A V)) :=
  lam.len_congr _ _ (((ModuleCat.extendScalars φ).leftDerivedZeroIsoSelf).app
    (ModuleCat.of A V)).toLinearEquiv

/-- λ-平坦性のもとで、有限なランクも剰余体のテンソル積だけで判定できる。 -/
theorem normalizedLength_tensor_rank_iff_residue
    (lam : NormalizedLength C ((maximalIdeal A).map φ))
    (hflat : ∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
      ∀ i : ℕ, 0 < i → lam.len (TorAlg φ i V) = 0)
    (r : ℝ≥0∞) (hr : r ≠ ⊤) :
    (∀ (V : Type u) [AddCommGroup V] [Module A V], IsFiniteLength A V →
      lam.len ((ModuleCat.extendScalars φ).obj (ModuleCat.of A V)) =
        r * ENat.toENNReal (Module.length A V)) ↔
    lam.len ((ModuleCat.extendScalars φ).obj (ModuleCat.of A (A ⧸ maximalIdeal A))) = r := by
  have : IsSimpleModule A (A ⧸ maximalIdeal A) := by
    rw [isSimpleModule_iff_isCoatom]
    exact Ideal.isMaximal_def.mp (maximalIdeal.isMaximal A)
  constructor
  · intro h
    simpa only [Module.length_eq_one, ENat.toENNReal_one, mul_one] using
      h _ (isFiniteLength_of_isSimpleModule (A ⧸ maximalIdeal A))
  · intro hk V _ _ hV
    rw [← normalizedLength_tor_zero_eq_tensor φ lam] at hk ⊢
    exact (normalizedLength_tor_of_residue φ lam r hr
      ((normalizedLength_tor_pos_eq_zero_iff_residue φ lam).mp hflat) hk V hV).2.1

end SerrePositivity

module

public import SerrePositivity.HomologicalAlgebra.TorLES
public import SerrePositivity.CommutativeAlgebra.TorFiniteLength
public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import SerrePositivity.PerfectComplex.NormalizedLength
public import SerrePositivity.CommutativeAlgebra.KoszulResolution
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Topology.Instances.ENNReal.ENatENNReal

/-!
# 有限長加群の Tor の正規化長さ

系2.6と補題3.4に共通する一般定理。仮定は

- `z` が `m_A` を生成する弱正則列であること（`A` は局所環）、
- `C` が `A` 代数であること（`φ : A →+* C`）、
- `λ` が `m_A C` の冪で消える `C` 加群の上で加法的・非負であること、
- Koszul ホモロジーの評価：`λ H_i(φ z; C) = 0 (i > 0)`、`λ(C/(φ z)C) = r`

である。結論は有限長 `A` 加群 `V` に対する公式：
`λ Tor_i^A(C, V) = 0 (i > 0)`、`λ Tor_0^A(C, V) = r · length_A V`、すべて有限。

証明は組成列の帰納法。`V = k = A/m` のときは Koszul 分解（`torAlgKoszulEquiv`）で
`Tor_i^A(C, k) ≅ H_i(φ z; C)`。一般の `V` は `0 → N → V → k → 0` の Tor 長完全列
（`torAlg_longExact`）と、`NormalizedLength` の完全列の評価による。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

variable [IsLocalRing A]

/-- 弱正則列の Koszul ホモロジーの評価から、有限長加群の Tor の正規化長さを計算する。 -/
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
  have hkfin : ∀ i : ℕ, lam.len (TorAlg φ i (A ⧸ maximalIdeal A)) ≠ ⊤ := by
    intro i
    rcases i with _ | i
    · rw [hk0]; exact ENNReal.natCast_ne_top r
    · rw [hkpos (i + 1) (by omega)]; exact ENNReal.zero_ne_top
  -- 組成列の帰納法
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

end SerrePositivity

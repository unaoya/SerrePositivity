module

public import SerrePositivity.IntersectionMultiplicity.ParameterQuotientTorBound
public import SerrePositivity.Paper.Section2.TowerApproximation
public import SerrePositivity.Inputs.RegularParameters
public import SerrePositivity.HomologicalAlgebra.FiniteFreeResolution

/-!
# パラメータ商とその有限近似（論文 §5.2–5.3、Lemma 5.3、5.4）

## 概要

§5.2 の設定：正則局所環 `R`（次元 `d`）、`R` 代数 `C`（`φ : R → C`、論文ではひねった作用
`ι_σ : R → D′ → C`）、`R` 正則列 `x = (x_1, …, x_h)`、`B = R/(x)`、`U = C/(x)C`。

- **Lemma 5.3**（`lemma_5_3`、証明済み）：有限生成 `B` 加群 `L` について
  `τ_i(L) := λ(Tor_i^B(U, L)) = λ(Tor_i^R(C, L))`、すべて有限、`i > d − h` で `0`。
  一般論 `ParamQuot.torClaim`、`ParamQuot.len_torAlg_eq_zero` に、正則局所環上の長さ `d` 以下の
  有限自由分解を与える。
- **Lemma 5.4**（`lemma_5_4`、主張のみ）：塔の近似の一般論
  （`Section2.exists_tower_approximation_B`）を `T = D′/I_σ`、`U = C/I_σ C` に適用したもの。

## 仮定の形

`λ` は `C` 上の正規化長さ（論文の `λ_D`）。`J` は有限生成で `J ⊆ √((x)C)`、`J^a ⊆ (x)C`
（論文では `J = 𝔡′C`、`I_σ` は `𝔡′` 準素）。Koszul ホモロジーの評価はすべての冪 `x^v` で仮定する
（Theorem 2.5 の (2.4)）。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal

namespace SerrePositivity

namespace Section5

open ParamQuot

variable {R C : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing C] (φ : R →+* C)
  {h : ℕ} (x : Fin h → R) {J : Ideal C} (lam : NormalizedLength C J)

/-- **Lemma 5.3**：`d = dim R`、`x` は `R` 正則列、`J` は有限生成で `J^a ⊆ (x)C ⊆ …`、`J ⊆ √((x)C)`、
`λ(H_q(x^v; C)) = 0`（`q, v > 0`）、`λ(U) < ∞` なら、有限生成 `B` 加群 `L` について
`λ(Tor_i^B(U, L)) = λ(Tor_i^R(C, L))`、有限、`i + h > d` で `0`。 -/
theorem lemma_5_3 {d : ℕ} (hd : ringKrullDim R = d)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x))
    (hfg : J.FG) {a : ℕ} (hJ : J ^ a ≤ IC φ x)
    (hJrad : J ≤ (Ideal.span (Set.range (φ ∘ x))).radical)
    (hzero : ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      lam.len (koszulHomologySelf (fun j ↦ φ (x j ^ v)) q) = 0)
    (hUfin : lam.len (U φ x) ≠ ⊤)
    (L : Type u) [AddCommGroup L] [Module R L] [Module (B x) L] [IsScalarTower R (B x) L]
    [Module.Finite (B x) L] (i : ℕ) :
    (lamU φ x lam).len (TorAlg (ψ φ x) i L) = lam.len (TorAlg φ i L) ∧
      lam.len (TorAlg φ i L) ≠ ⊤ ∧ (d < i + h → lam.len (TorAlg φ i L) = 0) := by
  have hzero1 : ∀ q : ℕ, 0 < q → lam.len (koszulHomologySelf (φ ∘ x) q) = 0 := by
    intro q hq
    have hfun : (fun j ↦ φ (x j ^ 1)) = φ ∘ x := funext fun j ↦ by simp
    have := hzero 1 one_pos q hq
    rwa [hfun] at this
  obtain ⟨e, he⟩ := torClaim hJ lam hreg hzero1 hUfin i L
  refine ⟨e, he, fun hi ↦ ?_⟩
  -- 長さ `d` 以下の有限自由分解
  obtain ⟨rs, hrs, hgen, hdim⟩ := exists_regular_generators R
  have hlen : rs.length = d := by
    have := hdim.symm.trans hd
    exact_mod_cast this
  have : Module.Finite R L := Module.Finite.trans (B x) L
  obtain ⟨P, hPlen, hPfree, hPfin⟩ :=
    exists_finite_free_resolution_of_regular_generators rs hrs hgen (ModuleCat.of R L)
  obtain ⟨F, ⟨hF⟩, hFb, hFfree, hFfin⟩ :=
    bounded_finite_free_cochain_of_projectiveResolution P rs.length hPlen hPfree hPfin
  have hL : ∀ j (l : L), x j • l = 0 := fun j l ↦ by
    rw [← algebraMap_smul (B x) (x j) l, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j)), zero_smul]
  exact len_torAlg_eq_zero φ x lam hfg hJrad hzero L hL F hF hFfree hFfin
    (fun k hk ↦ hFb k (Or.inl (by rw [hlen]; exact hk))) i (by rw [hlen] at *; omega)

/-- **Lemma 5.4**（主張のみ）：Lemma 5.3 の設定に、塔の基底 `A`（`t`、`p`）、`T = D′/I_σ`（`A` 上有限な
局所環で `m_A^a T = 0`、剰余体は `A` からも `B` からも全射）、`S = Λ ⊗_A T` の `U = C/(x)C` への作用
`θ`（`Λ` の作用と `B` の作用に両立）を加える。`λ` は `λ_∞` の `Λ → C` に沿った係数制限。このとき
有限長 `B` 加群の列 `M_n` と `s_n = p^{j_n h_A}` で、`T` を消す `B` のイデアルは `M_n` も消し、

- (5.9) `ℓ_B(M_n) / s_n → λ(U)`、
- (5.10) `ℓ_B(Tor_i^B(M_n, L_k)) / s_n → τ_i(L_k) = λ(Tor_i^R(C, L_k))`、
- (5.11) `B` のイデアル `I` が `T` を消すなら `λ(U) ≤ τ_0(k) · ℓ_B(B/I)`（`β₀(M_n) = ℓ_B(Tor_0^B(M_n, k))`）。

証明は `Section2.exists_tower_approximation_B` を `U` に適用し、`θ` の両立から `S` 加群としての長さと
`C` 加群としての長さが一致すること、`Tor^B(U, L)` の二つの計算（`S` 上の `U ⊗_B G` と `TorAlg ψ`）の
一致、Lemma 5.3 による `τ_i` との同定、`ℓ_B(M_n) ≤ β₀(M_n) ℓ_B(B/I)` の極限。 -/
theorem lemma_5_4 (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {hA : ℕ}
    (t : Fin hA → A) (p : ℕ) [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)
    (T : Type u) [CommRing T] [Algebra A T] [IsLocalRing T] [Module.Finite A T] {a : ℕ}
    (hTa : ∀ y ∈ maximalIdeal A ^ a, algebraMap A T y = 0)
    (hresT : Function.Surjective ((residue T).comp (algebraMap A T)))
    [Algebra (B x) T] (hresB : Function.Surjective ((residue T).comp (algebraMap (B x) T)))
    [Algebra (Section2.Tower A t p) C]
    (hJ' : (Section2.towerMaxIdeal A t p).map (algebraMap (Section2.Tower A t p) C) ≤ J)
    (hlam : lam = (Section2.towerLength A t p).comap (algebraMap (Section2.Tower A t p) C) J hJ')
    (θ : Section2.TS A t p T →+* U φ x)
    (hθΛ : θ.comp (algebraMap (Section2.Tower A t p) (Section2.TS A t p T)) =
      (Ideal.Quotient.mk (IC φ x)).comp (algebraMap (Section2.Tower A t p) C))
    (hθB : θ.comp (Section2.ψU A t p T (B x)) = ψ φ x)
    {d : ℕ} (hd : ringKrullDim R = d)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x))
    (hfg : J.FG) {b : ℕ} (hJ : J ^ b ≤ IC φ x)
    (hJrad : J ≤ (Ideal.span (Set.range (φ ∘ x))).radical)
    (hzero : ∀ v : ℕ, 0 < v → ∀ q : ℕ, 0 < q →
      lam.len (koszulHomologySelf (fun j ↦ φ (x j ^ v)) q) = 0)
    (hUfin : lam.len (U φ x) ≠ ⊤)
    {ι : Type*} (L : ι → Type u) [∀ k, AddCommGroup (L k)] [∀ k, Module R (L k)]
    [∀ k, Module (B x) (L k)] [∀ k, IsScalarTower R (B x) (L k)] [∀ k, Module.Finite (B x) (L k)]
    (G : ι → CochainComplex (ModuleCat.{u} (B x)) ℤ)
    (hG : ∀ k, IsResolutionOf (G k) (ModuleCat.of (B x) (L k)))
    (hfree : ∀ k i, Module.Free (B x) ((G k).X i)) (hfin : ∀ k i, Module.Finite (B x) ((G k).X i))
    [IsLocalRing (B x)] :
    ∃ (M : ℕ → ModuleCat.{u} (B x)) (s : ℕ → ℕ),
      (∀ n, IsFiniteLength (B x) (M n)) ∧ (∀ n, 0 < s n) ∧
      (0 < hA → Filter.Tendsto s Filter.atTop Filter.atTop) ∧
      (∀ (I : Ideal (B x)), (∀ y ∈ I, algebraMap (B x) T y = 0) →
        ∀ n, ∀ y ∈ I, ∀ m : M n, y • m = 0) ∧
      Filter.Tendsto (fun n ↦ (Module.length (B x) (M n) : ℝ≥0∞) / (s n : ℝ≥0∞)) Filter.atTop
        (nhds (lam.len (U φ x))) ∧
      (∀ k (i : ℕ), Filter.Tendsto
        (fun n ↦ (Module.length (B x) (TorModule (B x) i (M n) (L k)) : ℝ≥0∞) / (s n : ℝ≥0∞))
        Filter.atTop (nhds (lam.len (TorAlg φ i (L k))))) ∧
      (∀ (I : Ideal (B x)), (∀ y ∈ I, algebraMap (B x) T y = 0) →
        lam.len (U φ x) ≤ lam.len (TorAlg φ 0 (B x ⧸ maximalIdeal (B x))) *
          (Module.length (B x) (B x ⧸ I) : ℝ≥0∞)) := by
  sorry

end Section5

end SerrePositivity

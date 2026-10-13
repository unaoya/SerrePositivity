module

public import SerrePositivity.IntersectionMultiplicity.ParameterQuotientTorBound
public import SerrePositivity.Paper.Section2.TowerApproximation
public import SerrePositivity.CommutativeAlgebra.RegularParameters
public import SerrePositivity.HomologicalAlgebra.MinimalFreeResolution
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
- **Lemma 5.4**（`lemma_5_4`、証明済み）：塔の近似の一般論
  （`Section2.exists_tower_approximation_B`）を `T = D′/I_σ`、`U = C/I_σ C` に適用したもの。
  `S = Λ ⊗_A T` の `U` への作用 `θ` の両立から、`S` 加群と `C` 加群としての長さが一致し
  （`hE1`）、`Tor^B(U, L)` の二つの計算（`U ⊗_S (S ⊗_B G)` と `TorAlg ψ`）が一致する（`hE2`、
  `extendRestrictScalarsTensorIso` と `extendScalarsComp`）。(5.11) は
  `ℓ_B(M) ≤ β₀(M) · ℓ_B(B/I)`（`length_le_tor_zero_mul`）の極限。

## 仮定の形

`λ` は `C` 上の正規化長さ（論文の `λ_D`）。`J` は有限生成で `J ⊆ √((x)C)`、`J^a ⊆ (x)C`
（論文では `J = 𝔡′C`、`I_σ` は `𝔡′` 準素）。Koszul ホモロジーの評価はすべての冪 `x^v` で仮定する
（Theorem 2.5 の (2.4)）。
-/

@[expose] public section

universe u

open IsLocalRing CategoryTheory
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

/-! ## (5.11) の不等式 -/

section beta

/-- **`ℓ_B(M) ≤ β₀(M) · ℓ_B(B/I)`**：局所環 `B` 上の有限生成加群 `M` をイデアル `I` が消すなら、
`β₀(M) = ℓ_B(Tor_0^B(M, k)) = dim_k(k ⊗ M)` 個の元で生成され、`(B/I)^{β₀} ↠ M`。 -/
theorem length_le_tor_zero_mul {B : Type u} [CommRing B] [IsLocalRing B] (M : Type u)
    [AddCommGroup M] [Module B M] [Module.Finite B M] (I : Ideal B)
    (hI : ∀ y ∈ I, ∀ m : M, y • m = 0) :
    (Module.length B M : ℝ≥0∞) ≤
      (Module.length B (TorModule B 0 M (B ⧸ maximalIdeal B)) : ℝ≥0∞) *
        (Module.length B (B ⧸ I) : ℝ≥0∞) := by
  classical
  let k := ResidueField B
  let n := Module.finrank k (TensorProduct B k M)
  let bk := Module.finBasis k (TensorProduct B k M)
  -- 基底の持ち上げ
  have hlift : ∀ i, ∃ m : M, (1 : k) ⊗ₜ[B] m = bk i := fun i ↦
    TensorProduct.mk_surjective B M k Ideal.Quotient.mk_surjective (bk i)
  choose f hf using hlift
  have hspan : Submodule.span B (Set.range f) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis f bk hf
  -- `(B/I)^n ↠ M`
  let gi : Fin n → (B ⧸ I) →ₗ[B] M := fun i ↦
    I.liftQ (LinearMap.toSpanSingleton B M (f i)) (fun y hy ↦ by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hI y hy (f i))
  let g : (Fin n → B ⧸ I) →ₗ[B] M := ∑ i, (gi i).comp (LinearMap.proj i)
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (Submodule.Quotient.mk 1), ?_⟩
    simp only [g, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i (fun x _ hx ↦ by rw [Pi.single_eq_of_ne hx, map_zero])
      (by simp), Pi.single_eq_same, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply,
      one_smul]
  have hle := Module.length_le_of_surjective g hg
  rw [Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hle
  -- `ℓ_B(Tor_0) = n`
  have htor : Module.length B (TorModule B 0 M (B ⧸ maximalIdeal B)) = n := by
    rw [((torModuleZeroEquiv B M (B ⧸ maximalIdeal B)).trans
      (TensorProduct.comm B M (B ⧸ maximalIdeal B))).length_eq]
    change Module.length B (TensorProduct B k M) = _
    rw [Module.length_eq_of_surjective (S := B) (R := k) Ideal.Quotient.mk_surjective,
      Module.length_eq_finrank]
  rw [htor]
  have := ENat.toENNReal_le.mpr hle
  simpa [ENat.toENNReal_mul] using this

end beta

/-- **Lemma 5.4**：Lemma 5.3 の設定に、塔の基底 `A`（`t`、`p`）、`T = D′/I_σ`（`A` 上有限な
局所環で `m_A^a T = 0`、剰余体は `A` からも `B` からも全射）、`S = Λ ⊗_A T` の `U = C/(x)C` への作用
`θ`（`Λ` の作用と `B` の作用に両立）を加える。`λ` は `λ_∞` の `Λ → C` に沿った係数制限。このとき
有限長 `B` 加群の列 `M_n` と `s_n = p^{j_n h_A}` で、`T` を消す `B` のイデアルは `M_n` も消し、

- (5.9) `ℓ_B(M_n) / s_n → λ(U)`、
- (5.10) `ℓ_B(Tor_i^B(M_n, L_k)) / s_n → τ_i(L_k) = λ(Tor_i^R(C, L_k))`、
- (5.11) `B` のイデアル `I` が `T` を消し `B/I` が有限長なら `λ(U) ≤ τ_0(k) · ℓ_B(B/I)`
  （`β₀(M_n) = ℓ_B(Tor_0^B(M_n, k))`）。

剰余体係数の全次数の Tor 極限も、同じ列について結論に含める。
`L_k` と剰余体の分解は Noether 局所環 `B` 上の極小自由分解から構成する。
分解の指定や `B` の正則性・分解の有界性を追加の仮定にしない。

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
    (hlam : lam = (Section2.towerLength A t p ht).comap (algebraMap (Section2.Tower A t p) C) J hJ')
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
      (∀ i : ℕ, Filter.Tendsto
        (fun n ↦ (Module.length (B x)
          (TorModule (B x) i (M n) (B x ⧸ maximalIdeal (B x))) : ℝ≥0∞) / (s n : ℝ≥0∞))
        Filter.atTop (nhds (lam.len (TorAlg φ i (B x ⧸ maximalIdeal (B x)))))) ∧
      (∀ (I : Ideal (B x)), (∀ y ∈ I, algebraMap (B x) T y = 0) →
        Module.length (B x) (B x ⧸ I) ≠ ⊤ →
        lam.len (U φ x) ≤ lam.len (TorAlg φ 0 (B x ⧸ maximalIdeal (B x))) *
          (Module.length (B x) (B x ⧸ I) : ℝ≥0∞)) := by
  classical
  let G (k : ι) := extRes (MinimalFreeResolution.resolution (FGModuleCat.of (B x) (L k)))
  let hG (k : ι) :=
    isResolutionOf_extRes (MinimalFreeResolution.resolution (FGModuleCat.of (B x) (L k)))
  have hfree (k : ι) (i : ℤ) : Module.Free (B x) ((G k).X i) := inferInstance
  have hfin (k : ι) (i : ℤ) : Module.Finite (B x) ((G k).X i) := inferInstance
  let G₀ := extRes (MinimalFreeResolution.resolution
    (FGModuleCat.of (B x) (B x ⧸ maximalIdeal (B x))))
  let hG₀ := isResolutionOf_extRes (MinimalFreeResolution.resolution
    (FGModuleCat.of (B x) (B x ⧸ maximalIdeal (B x))))
  have hfree₀ (i : ℤ) : Module.Free (B x) (G₀.X i) := inferInstance
  have hfin₀ (i : ℤ) : Module.Finite (B x) (G₀.X i) := inferInstance
  subst hlam
  let lam₀ := (Section2.towerLength A t p ht).comap (algebraMap (Section2.Tower A t p) C) J hJ'
  let S := Section2.TS A t p T
  let _ : Algebra S (U φ x) := θ.toAlgebra
  let US : ModuleCat.{u} S := ModuleCat.of S (U φ x)
  -- (E1) `S` 加群としての長さと `C` 加群としての長さ
  have hE1 : ∀ W : ModuleCat.{u} (U φ x),
      (Section2.μT A t p ht T).len ((ModuleCat.restrictScalars θ).obj W) =
        (lamU φ x lam₀).len W := by
    intro W
    change @Section2.towerLengthFun A _ _ t p W _
        (Module.compHom W (θ.comp (algebraMap (Section2.Tower A t p) S))) =
      @Section2.towerLengthFun A _ _ t p W _
        (Module.compHom W ((Ideal.Quotient.mk (IC φ x)).comp
          (algebraMap (Section2.Tower A t p) C)))
    rw [hθΛ]
  -- `U` 自身：自己加群を `C → U` で制限したものは商加群
  have hUself : (lamU φ x lam₀).len (ModuleCat.of (U φ x) (U φ x)) = lam₀.len (U φ x) := by
    rw [NormalizedLength.comap_len]
    congr 1
  have hUeq : (Section2.μT A t p ht T).len US = lam₀.len (U φ x) :=
    (hE1 (ModuleCat.of (U φ x) (U φ x))).trans hUself
  -- ねじれ
  have hUt : IsPowTorsion (Section2.JT A t p T) US := by
    have hle : (Section2.JT A t p T).map θ ≤ J.map (Ideal.Quotient.mk (IC φ x)) := by
      rw [Section2.JT, Ideal.map_map, hθΛ, ← Ideal.map_map]
      exact Ideal.map_mono hJ'
    exact IsPowTorsion.comap θ hle (U φ x) (isPowTorsion_U hJ (U φ x))
  -- (E2) `Tor^B(U, L)` の二つの計算と Lemma 5.3
  have hE2 : ∀ (L' : Type u) [AddCommGroup L'] [Module R L'] [Module (B x) L']
      [IsScalarTower R (B x) L'] [Module.Finite (B x) L']
      (G' : CochainComplex (ModuleCat.{u} (B x)) ℤ)
      (_ : IsResolutionOf G' (ModuleCat.of (B x) L')) (i : ℕ),
      (Section2.μT A t p ht T).len
        ((TensorRes.tensorRes (Section2.ψU A t p T (B x)) G' US).homology (-(i : ℤ))) =
        lam₀.len (TorAlg φ i L') := by
    intro L' _ _ _ _ _ G' hG' i
    let ψS := Section2.ψU A t p T (B x)
    let e₁ := ((Functor.mapHomologicalComplexCompIso
      (extendRestrictScalarsTensorIso (R := S) (T := U φ x)) (ComplexShape.up ℤ)).app
        (TensorRes.GS ψS G')).symm
    let e₂ := (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp ψS θ).symm
      (ComplexShape.up ℤ)).app G'
    let e := e₁ ≪≫ ((ModuleCat.restrictScalars θ).mapHomologicalComplex _).mapIso e₂
    let eh := (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso e ≪≫
      ((baseChange (θ.comp ψS) G').sc (-(i : ℤ))).mapHomologyIso (ModuleCat.restrictScalars θ)
    refine ((Section2.μT A t p ht T).len_congr _ _ eh.toLinearEquiv).trans ?_
    rw [hE1]
    refine ((lamU φ x lam₀).len_congr _ _
      (torIsoCochain (θ.comp ψS) hG' i).toLinearEquiv).symm.trans ?_
    rw [hθB]
    exact (lemma_5_3 φ x lam₀ hd hreg hfg hJ hJrad hzero hUfin L' i).1
  -- 剰余体を加えた族
  let L' : Option ι → Type u := fun o ↦ match o with
    | none => B x ⧸ maximalIdeal (B x)
    | some k => L k
  let iL₁ : ∀ o, AddCommGroup (L' o) := fun o ↦ match o with
    | none => inferInstanceAs (AddCommGroup (B x ⧸ maximalIdeal (B x)))
    | some k => inferInstanceAs (AddCommGroup (L k))
  let iL₂ : ∀ o, Module (B x) (L' o) := fun o ↦ match o with
    | none => inferInstanceAs (Module (B x) (B x ⧸ maximalIdeal (B x)))
    | some k => inferInstanceAs (Module (B x) (L k))
  let G' : Option ι → CochainComplex (ModuleCat.{u} (B x)) ℤ := fun o ↦ match o with
    | none => G₀
    | some k => G k
  have hG' : ∀ o, IsResolutionOf (G' o) (ModuleCat.of (B x) (L' o)) := fun o ↦ match o with
    | none => hG₀
    | some k => hG k
  have hfree' : ∀ o i, Module.Free (B x) ((G' o).X i) := fun o ↦ match o with
    | none => hfree₀
    | some k => hfree k
  have hfin' : ∀ o i, Module.Finite (B x) ((G' o).X i) := fun o ↦ match o with
    | none => hfin₀
    | some k => hfin k
  obtain ⟨M, s, hMfl, hspos, hsinf, hann, hlen, htor⟩ :=
    Section2.exists_tower_approximation_B A t p T ht hTa hresT hresB L' G' hG' hfree' hfin' US hUt
      (hUeq.trans_ne hUfin)
  refine ⟨M, s, hMfl, hspos, hsinf, hann, hUeq ▸ hlen,
    fun k i ↦ ?_, fun i ↦ ?_, fun I hI hIfin ↦ ?_⟩
  · have := htor (some k) i
    rwa [hE2 (L k) (G k) (hG k) i] at this
  · have := htor none i
    rwa [hE2 (B x ⧸ maximalIdeal (B x)) G₀ hG₀ i] at this
  · -- (5.11)
    have h0 := htor none 0
    rw [hE2 (B x ⧸ maximalIdeal (B x)) G₀ hG₀ 0] at h0
    refine le_of_tendsto_of_tendsto' (hUeq ▸ hlen)
      (ENNReal.Tendsto.mul_const h0 (Or.inr (ENat.toENNReal_ne_top.mpr hIfin))) fun n ↦ ?_
    have : Module.Finite (B x) (M n) :=
      have := (isFiniteLength_iff_isNoetherian_isArtinian.mp (hMfl n)).1
      Module.IsNoetherian.finite _ _
    have hb := length_le_tor_zero_mul (M n) I (hann I hI n)
    calc (Module.length (B x) (M n) : ℝ≥0∞) / (s n : ℝ≥0∞)
        ≤ ((Module.length (B x) (TorModule (B x) 0 (M n) (B x ⧸ maximalIdeal (B x))) : ℝ≥0∞) *
            (Module.length (B x) (B x ⧸ I) : ℝ≥0∞)) / (s n : ℝ≥0∞) :=
          ENNReal.div_le_div_right hb _
      _ = _ := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]

end Section5

end SerrePositivity

module

public import SerrePositivity.CommutativeAlgebra.PresentationBaseChange
public import SerrePositivity.Paper.Section2.TowerLength
public import SerrePositivity.Paper.Section2.TowerStage

/-!
# 段への降下（Lemma 2.3 (b) の標準事実 (S1)、(S2)）

## 概要

塔 `Λ = lim→ A_n` の加群に関する有限的なデータ（有限個の元、有限個の関係式、有限表示、有限表示な
加群の間の写像）は、どれかの段 `A_n` にすでに現れる。この「降下」を使って、`TowerLength.lean` の
標準事実

- (S2) `exists_descent`：`m_A` 冪ねじれで有限表示な `Λ` 加群 `M` は、ある段の有限長 `A_n` 加群 `V`
  から `M ≃ Λ ⊗_{A_n} V` と得られる、
- (S1) `fgLength_tensor`：有限長 `A_n` 加群 `V` で `λ*(Λ ⊗_{A_n} V) = ℓ_{A_n}(V) / p^{nh}`

を証明し、(2.2) `towerLengthFun_tensor` を (C1) と (S1) から導く。

## 方針

- 道具：`Λ` の有限個の元は共通の段から来る（`exists_towerOf_family`）、段の有限個の元が `Λ` で `0`
  ならある段で `0`（`exists_towerMap_eq_zero`、`Ring.DirectLimit.of.zero_exact`）、
  段の元の有限族の像が `Λ` で `span` に入るならある段で `span` に入る（`exists_stage_mem_span`）。
- (S2)：`M ≃ Λ^l / span k`（`Module.FinitePresentation.exists_fin`）。`k` の成分を段 `m` に持ち上げ
  `c`、ねじれ `m_A^e M = 0` から `x_σ e_i ∈ span k`（`x` は `m_A^e` の生成元）、これを段 `N ≥ m` に
  降ろす。`V := A_N^l / span (c の像)` は `(m_A A_N)^e` で消え、`A` 上有限なので有限長で、
  `Λ ⊗_{A_N} V ≃ Λ^l / span k ≃ M`（`baseChangeQuotEquiv`）。

## 規約

段 `m` の `ι` 組 `v : ι → A_m` に対し、`stageToTower m v : ι → Λ`（各成分に `towerOf m`）と
`stageToStage m m' v : ι → A_{m'}`（各成分に `towerMap m m'`）を使う。
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity

namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-! ## 道具：段の `ι` 組と `Λ` の `ι` 組 -/

section tools

variable {ι : Type*}

/-- 段 `m` の `ι` 組を `Λ` の `ι` 組へ（各成分に `towerOf m`）。`A_m` 線形。 -/
noncomputable abbrev stageToTower (m : ℕ) :
    (ι → TowerStage A t p m) →ₗ[TowerStage A t p m] (ι → Tower A t p) :=
  piAlgebraMap (TowerStage A t p m) (Tower A t p) ι

/-- 段 `m` の `ι` 組を段 `m'` へ（各成分に `towerMap m m'`）。`A` 線形。 -/
noncomputable def stageToStage (m m' : ℕ) (hmm' : m ≤ m') :
    (ι → TowerStage A t p m) →ₗ[A] (ι → TowerStage A t p m') :=
  LinearMap.compLeft (towerMap A t p m m' hmm').toLinearMap ι

lemma stageToTower_apply (m : ℕ) (v : ι → TowerStage A t p m) (i : ι) :
    stageToTower A t p m v i = towerOf A t p m (v i) := rfl

lemma stageToStage_apply (m m' : ℕ) (hmm' : m ≤ m') (v : ι → TowerStage A t p m) (i : ι) :
    stageToStage A t p m m' hmm' v i = towerMap A t p m m' hmm' (v i) := rfl

lemma stageToTower_single [DecidableEq ι] (m : ℕ) (i : ι) (a : TowerStage A t p m) :
    stageToTower A t p m (Pi.single i a) = Pi.single i (towerOf A t p m a) :=
  piAlgebraMap_single i a

lemma stageToStage_single [DecidableEq ι] (m m' : ℕ) (hmm' : m ≤ m') (i : ι)
    (a : TowerStage A t p m) :
    stageToStage A t p m m' hmm' (Pi.single i a) = Pi.single i (towerMap A t p m m' hmm' a) := by
  ext j
  by_cases hj : j = i
  · subst hj; simp [stageToStage_apply]
  · simp [stageToStage_apply, hj]

lemma stageToTower_stageToStage (m m' : ℕ) (hmm' : m ≤ m') (v : ι → TowerStage A t p m) :
    stageToTower A t p m' (stageToStage A t p m m' hmm' v) = stageToTower A t p m v :=
  funext fun i ↦ towerOf_towerMap A t p m m' hmm' (v i)

lemma stageToStage_stageToStage (m₁ m₂ m₃ : ℕ) (h₁₂ : m₁ ≤ m₂) (h₂₃ : m₂ ≤ m₃)
    (v : ι → TowerStage A t p m₁) :
    stageToStage A t p m₂ m₃ h₂₃ (stageToStage A t p m₁ m₂ h₁₂ v) =
      stageToStage A t p m₁ m₃ (h₁₂.trans h₂₃) v :=
  funext fun i ↦ towerMap_towerMap A t p m₁ m₂ m₃ h₁₂ h₂₃ (v i)

lemma stageToStage_smul (m m' : ℕ) (hmm' : m ≤ m') (a : TowerStage A t p m)
    (v : ι → TowerStage A t p m) :
    stageToStage A t p m m' hmm' (a • v) =
      towerMap A t p m m' hmm' a • stageToStage A t p m m' hmm' v := by
  funext i
  simp only [stageToStage_apply, Pi.smul_apply, smul_eq_mul, map_mul]

lemma stageToTower_smul (m : ℕ) (a : TowerStage A t p m) (v : ι → TowerStage A t p m) :
    stageToTower A t p m (a • v) = towerOf A t p m a • stageToTower A t p m v := by
  rw [map_smul, ← algebraMap_smul (Tower A t p) a (stageToTower A t p m v)]
  rfl

/-- **span 所属の降下**：段 `m` の元の有限族 `w` の `Λ` での像が、`c` の像の張る `Λ` 部分加群に
入るなら、ある段 `m' ≥ m` で `w` の像が `c` の像の張る `A_{m'}` 部分加群に入る。
係数を段に持ち上げ、差が `Λ` で `0` になることから、さらに先の段で `0` になる。 -/
lemma exists_stage_mem_span [Finite ι] {κ σ : Type*} [Finite κ] [Finite σ] (m : ℕ)
    (c : κ → (ι → TowerStage A t p m)) (w : σ → (ι → TowerStage A t p m))
    (hw : ∀ s, stageToTower A t p m (w s) ∈
      Submodule.span (Tower A t p) (Set.range (stageToTower A t p m ∘ c))) :
    ∃ (m' : ℕ) (hmm' : m ≤ m'), ∀ s, stageToStage A t p m m' hmm' (w s) ∈
      Submodule.span (TowerStage A t p m') (Set.range (stageToStage A t p m m' hmm' ∘ c)) := by
  classical
  cases nonempty_fintype σ
  cases nonempty_fintype κ
  -- 係数 `lam s j ∈ Λ`
  have hw' : ∀ s, ∃ lam : κ → Tower A t p,
      ∑ j, lam j • stageToTower A t p m (c j) = stageToTower A t p m (w s) := fun s ↦ by
    simpa [Function.comp_def] using
      (Submodule.mem_span_range_iff_exists_fun (Tower A t p)).mp (hw s)
  choose lam hlam using hw'
  -- 係数を段 `m₁` に持ち上げる
  obtain ⟨m₁, mu, hmu⟩ := exists_towerOf_family A t p (fun sj : σ × κ ↦ lam sj.1 sj.2)
  have hm : m ≤ m ⊔ m₁ := le_sup_left
  have hm₁ : m₁ ≤ m ⊔ m₁ := le_sup_right
  -- 段 `m ⊔ m₁` での差は `Λ` で `0`
  let z : σ → (ι → TowerStage A t p (m ⊔ m₁)) := fun s ↦
    stageToStage A t p m _ hm (w s) -
      ∑ j, towerMap A t p m₁ _ hm₁ (mu (s, j)) • stageToStage A t p m _ hm (c j)
  have hz : ∀ si : σ × ι, towerOf A t p _ (z si.1 si.2) = 0 := by
    rintro ⟨s, i⟩
    have : stageToTower A t p _ (z s) = 0 := by
      simp only [z, map_sub, map_sum, stageToTower_smul, stageToTower_stageToStage,
        towerOf_towerMap, hmu, hlam, sub_self]
    exact congr_fun this i
  obtain ⟨m₃, h₂₃, hz'⟩ := exists_towerMap_eq_zero A t p _ (fun si : σ × ι ↦ z si.1 si.2) hz
  refine ⟨m₃, hm.trans h₂₃, fun s ↦ ?_⟩
  have hzs : stageToStage A t p _ m₃ h₂₃ (z s) = 0 := funext fun i ↦ hz' (s, i)
  simp only [z, map_sub, map_sum, stageToStage_smul, stageToStage_stageToStage, sub_eq_zero] at hzs
  rw [hzs]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end tools

/-! ## (S2) 降下 -/

section descent

variable [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime]

/-- (S2) **降下**：`m_A` 冪ねじれで有限表示な `Λ` 加群は、ある段 `n` の有限長 `A_n` 加群 `V` から
`Λ ⊗_{A_n} V` として得られる。`A` は Noether（`m_A^e` が有限生成であることに使う）。 -/
theorem exists_descent (M : Type u) [AddCommGroup M] [Module (Tower A t p) M]
    [Module.FinitePresentation (Tower A t p) M] (hM : IsPowTorsion (towerMaxIdeal A t p) M) :
    ∃ (n : ℕ) (V : Type u) (_ : AddCommGroup V) (_ : Module (TowerStage A t p n) V),
      IsFiniteLength (TowerStage A t p n) V ∧
        IsPowTorsion ((maximalIdeal A).map (algebraMap A (TowerStage A t p n))) V ∧
        Nonempty (M ≃ₗ[Tower A t p] Tower A t p ⊗[TowerStage A t p n] V) := by
  classical
  -- 有限表示 `M ≃ Λ^l / K`、`K = span k`
  obtain ⟨l, K, e, hK⟩ := Module.FinitePresentation.exists_fin (Tower A t p) M
  obtain ⟨b, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  -- 生成元を段 `m` に持ち上げる
  obtain ⟨m, z, hz⟩ := exists_towerOf_family A t p (fun ji : Fin b × Fin l ↦ k ji.1 ji.2)
  let c : Fin b → (Fin l → TowerStage A t p m) := fun j i ↦ z (j, i)
  have hc : stageToTower A t p m ∘ c = k := funext fun j ↦ funext fun i ↦ hz (j, i)
  -- ねじれ：`m_A^e₀` の生成元 `x`
  obtain ⟨e₀, he⟩ := hM
  obtain ⟨s, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (maximalIdeal A ^ e₀))
  have hxmem : ∀ σ, algebraMap A (Tower A t p) (x σ) ∈ towerMaxIdeal A t p ^ e₀ := fun σ ↦ by
    dsimp only [towerMaxIdeal]
    rw [← Ideal.map_pow, ← hx]
    exact Ideal.mem_map_of_mem _ (Submodule.subset_span ⟨σ, rfl⟩)
  -- `x_σ e_i ∈ K`
  have hxK : ∀ (σ : Fin s) (i : Fin l),
      algebraMap A (Tower A t p) (x σ) • Pi.single i (1 : Tower A t p) ∈ K := by
    intro σ i
    obtain ⟨y, hy⟩ := e.surjective (Submodule.Quotient.mk (Pi.single i 1))
    have h0 : algebraMap A (Tower A t p) (x σ) • y = 0 := he (a := ⟨_, hxmem σ⟩)
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, ← hy, ← map_smul, h0,
      map_zero]
  -- 段 `m` の元 `w σ i := x_σ e_i` の像は `Λ` で `span (ρ c)` に入る
  have hw : ∀ σi : Fin s × Fin l,
      stageToTower A t p m (algebraMap A (TowerStage A t p m) (x σi.1) •
        Pi.single σi.2 (1 : TowerStage A t p m)) ∈
        Submodule.span (Tower A t p) (Set.range (stageToTower A t p m ∘ c)) := by
    rintro ⟨σ, i⟩
    rw [hc, hk, stageToTower_smul, stageToTower_single, map_one, ← algebraMap_towerStage_apply,
      ← IsScalarTower.algebraMap_apply]
    exact hxK σ i
  obtain ⟨N, hmN, hN⟩ := exists_stage_mem_span A t p m c _ hw
  -- 降りた加群 `V := A_N^l / span d`
  let d : Fin b → (Fin l → TowerStage A t p N) := stageToStage A t p m N hmN ∘ c
  let KN : Submodule (TowerStage A t p N) (Fin l → TowerStage A t p N) :=
    Submodule.span _ (Set.range d)
  -- `V` は `(m_A A_N)^e₀` で消える
  have htor : Module.IsTorsionBySet (TowerStage A t p N) ((Fin l → TowerStage A t p N) ⧸ KN)
      (((maximalIdeal A).map (algebraMap A (TowerStage A t p N)) ^ e₀ : Ideal _) : Set _) := by
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe, ← Ideal.map_pow,
      ← hx, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Module.mem_annihilator]
    intro v
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, pi_eq_sum_univ' v,
      Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [smul_comm]
    refine Submodule.smul_mem _ _ ?_
    have := hN (σ, i)
    rwa [stageToStage_smul, stageToStage_single, map_one, AlgHom.commutes] at this
  refine ⟨N, (Fin l → TowerStage A t p N) ⧸ KN, inferInstance, inferInstance, ?_, ⟨e₀, htor⟩, ?_⟩
  · -- 有限長：`A` 上有限で `m_A^e₀` で消えるので `A` 上有限長、塔で `A_N` 上へ
    have hfinA : Module.Finite A (TowerStage A t p N) := towerStage_finite A t p N
    have hfin : Module.Finite A ((Fin l → TowerStage A t p N) ⧸ KN) :=
      Module.Finite.trans (TowerStage A t p N) _
    have hArt : IsArtinianRing (A ⧸ maximalIdeal A) :=
      inferInstanceAs (IsArtinianRing (ResidueField A))
    have hfl : IsFiniteLength A ((Fin l → TowerStage A t p N) ⧸ KN) := by
      refine isFiniteLength_of_le_radical_annihilator (maximalIdeal A) _ fun a ha ↦
        Ideal.mem_radical_iff.mpr ⟨e₀, ?_⟩
      rw [Module.mem_annihilator]
      intro v
      have hmem : algebraMap A (TowerStage A t p N) (a ^ e₀) ∈
          (maximalIdeal A).map (algebraMap A (TowerStage A t p N)) ^ e₀ := by
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow ha e₀)
      rw [← algebraMap_smul (TowerStage A t p N) (a ^ e₀) v]
      exact htor (a := ⟨_, hmem⟩)
    obtain ⟨hN', hA'⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_of_tower A hN', isArtinian_of_tower A hA'⟩
  · -- `Λ ⊗_{A_N} V ≃ Λ^l / span k ≃ M`
    have hK' : K = Submodule.span (Tower A t p)
        (Set.range (piAlgebraMap (TowerStage A t p N) (Tower A t p) (Fin l) ∘ d)) := by
      rw [← hk, ← hc]
      congr 2
      funext j
      exact (stageToTower_stageToStage A t p m N hmN (c j)).symm
    exact ⟨e.trans ((Submodule.quotEquivOfEq _ _ hK').trans
      (baseChangeQuotEquiv (Tower A t p) d).symm)⟩

end descent

/-! ## (S1) 有限段の公式

### 方針

`λ*(Λ ⊗_{A_n} V) ≤ ℓ(V)/p^{nh}` は定義（`P := Λ ⊗ V`、`f := id`、降下 `(n, V)`）。逆向きには、
有限表示な全射 `f : P ↠ Λ ⊗_{A_n} V` と降下 `P ≃ Λ ⊗_{A_m} W` をとり、`ℓ(V)/p^{nh} ≤ ℓ(W)/p^{mh}` を示す：

1. 共通の段 `N = n ⊔ m` に上げる：`Λ ⊗_{A_n} V ≃ Λ ⊗_{A_N} (A_N ⊗_{A_n} V)`（`cancelBaseChange`）で、
   `ℓ_{A_N}(A_N ⊗_{A_n} V) = p^{(N−n)h} ℓ_{A_n}(V)`（`length_tensor_towerMap`：
   `A_N ≅ A_n^{p^{(N−n)h}}` と剰余体の一致）。
2. `A_N ⊗ V`、`A_N ⊗ W` を有限表示 `A_N^c / span s`、`A_N^a / span r` で表し、`Λ` 線形な全射
   `Λ^a / span (ρ r) ↠ Λ^c / span (ρ s)` を段 `N' ≥ N` に降ろす（`exists_stage_surjective`：生成元の像と
   関係式・全射性の証人を段に持ち上げ、`exists_stage_mem_span` で `span` 所属を降ろす）。
3. 段 `N'` で長さを比べ（`Module.length_le_of_surjective`）、再び `length_tensor_towerMap` で
   `p^{(N'−n)h} ℓ(V) ≤ p^{(N'−m)h} ℓ(W)`、両辺を `p^{N'h}` で割る。 -/

section stage

variable (n N : ℕ) (hnN : n ≤ N)

/-- `A → A_n → A_N` は可換（`A_N` を `towerMap n N` で `A_n` 代数とみる）。 -/
lemma isScalarTower_towerMap :
    letI := (towerMap A t p n N hnN).toRingHom.toAlgebra
    IsScalarTower A (TowerStage A t p n) (TowerStage A t p N) :=
  letI := (towerMap A t p n N hnN).toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun x ↦ ((towerMap A t p n N hnN).commutes x).symm

/-- `A_n → A_N → Λ` は可換。 -/
lemma isScalarTower_towerMap_tower :
    letI := (towerMap A t p n N hnN).toRingHom.toAlgebra
    IsScalarTower (TowerStage A t p n) (TowerStage A t p N) (Tower A t p) :=
  letI := (towerMap A t p n N hnN).toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun x ↦ (towerOf_towerMap A t p n N hnN x).symm

variable [IsLocalRing A] [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)

set_option linter.style.haveILetI false in
include ht in
/-- `A_n → A_N → k_N` は全射（剰余体はどの段でも `k`）。 -/
lemma residue_surjective_towerMap :
    letI := (towerMap A t p n N hnN).toRingHom.toAlgebra
    haveI := isLocalRing_towerStage A t p ht N
    Function.Surjective ((residue (TowerStage A t p N)).comp
      (algebraMap (TowerStage A t p n) (TowerStage A t p N))) := by
  letI := (towerMap A t p n N hnN).toRingHom.toAlgebra
  haveI := isLocalRing_towerStage A t p ht N
  haveI := isScalarTower_towerMap A t p n N hnN
  have h := residue_surjective_towerStage A t p ht N
  rw [IsScalarTower.algebraMap_eq A (TowerStage A t p n) (TowerStage A t p N),
    ← RingHom.comp_assoc, RingHom.coe_comp] at h
  exact h.of_comp

set_option linter.style.haveILetI false in
include ht in
/-- **段の間の係数拡大の長さ**：`ℓ_{A_N}(A_N ⊗_{A_n} V) = p^{(N−n)h} · ℓ_{A_n}(V)`。
`A_N ≅ A_n^{p^{(N−n)h}}` なので `A_N ⊗ V ≅ V^{p^{(N−n)h}}`、長さは剰余体が同じなので `A_n` 上でも
`A_N` 上でも同じ（`length_eq_of_common_residueField`）。 -/
lemma length_tensor_towerMap (V : Type u) [AddCommGroup V] [Module (TowerStage A t p n) V] :
    letI := (towerMap A t p n N hnN).toRingHom.toAlgebra
    Module.length (TowerStage A t p N) (TowerStage A t p N ⊗[TowerStage A t p n] V) =
      (stageRank h p (N - n) : ℕ∞) * Module.length (TowerStage A t p n) V := by
  classical
  letI := (towerMap A t p n N hnN).toRingHom.toAlgebra
  haveI := isLocalRing_towerStage A t p ht N
  rw [← length_eq_of_common_residueField (residue_surjective_towerMap A t p n N hnN ht)]
  let e : (TowerStage A t p N ⊗[TowerStage A t p n] V) ≃ₗ[TowerStage A t p n]
      ((Fin h → Fin (p ^ (N - n))) →₀ V) :=
    (TensorProduct.congr (towerMapBasis A t p n N hnN).repr (LinearEquiv.refl _ V)).trans
      (TensorProduct.finsuppScalarLeft _ _ _)
  rw [e.length_eq, Module.length_finsupp, ENat.card_eq_coe_fintype_card, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, stageRank, pow_mul]

end stage

/-! ### 全射の降下 -/

/-- **全射の降下**：段 `N` で表示された二つの加群の `Λ` への係数拡大の間に `Λ` 線形な全射があれば、
ある段 `N' ≥ N` で、`A_{N'}` への係数拡大の間に `A_{N'}` 線形な全射がある。
生成元の像 `u_i` と、関係式・全射性の証人を段に持ち上げ、`exists_stage_mem_span` で降ろす。 -/
lemma exists_stage_surjective {a b c d : ℕ} (N : ℕ) (r : Fin b → (Fin a → TowerStage A t p N))
    (s : Fin d → (Fin c → TowerStage A t p N))
    (g : ((Fin a → Tower A t p) ⧸ Submodule.span (Tower A t p)
        (Set.range (stageToTower A t p N ∘ r))) →ₗ[Tower A t p]
      ((Fin c → Tower A t p) ⧸ Submodule.span (Tower A t p)
        (Set.range (stageToTower A t p N ∘ s))))
    (hg : Function.Surjective g) :
    ∃ (N' : ℕ) (hNN' : N ≤ N')
      (g' : ((Fin a → TowerStage A t p N') ⧸ Submodule.span (TowerStage A t p N')
          (Set.range (stageToStage A t p N N' hNN' ∘ r))) →ₗ[TowerStage A t p N']
        ((Fin c → TowerStage A t p N') ⧸ Submodule.span (TowerStage A t p N')
          (Set.range (stageToStage A t p N N' hNN' ∘ s)))),
      Function.Surjective g' := by
  classical
  -- 生成元の像の持ち上げ `u i ∈ Λ^c`、`e_k` の原像 `v' k ∈ Λ^a`
  choose u hu using fun i : Fin a ↦
    Submodule.Quotient.mk_surjective _ (g (Submodule.Quotient.mk (Pi.single i 1)))
  choose v hv using fun k : Fin c ↦ hg (Submodule.Quotient.mk (Pi.single k 1))
  choose v' hv' using fun k ↦ Submodule.Quotient.mk_surjective _ (v k)
  -- `g [w] = [∑ i, w i • u i]`
  have hgmk : ∀ w : Fin a → Tower A t p,
      g (Submodule.Quotient.mk w) = Submodule.Quotient.mk (∑ i, w i • u i) := by
    intro w
    conv_lhs => rw [pi_eq_sum_univ' w]
    rw [← Submodule.mkQ_apply, ← Submodule.mkQ_apply]
    simp only [map_sum, map_smul, Submodule.mkQ_apply, ← hu]
  -- 成分を段 `N₁` に持ち上げる
  obtain ⟨N₁, z, hz⟩ := exists_towerOf_family A t p
    (Sum.elim (fun ik : Fin a × Fin c ↦ u ik.1 ik.2) (fun ki : Fin c × Fin a ↦ v' ki.1 ki.2))
  have hN : N ≤ N ⊔ N₁ := le_sup_left
  have hN₁ : N₁ ≤ N ⊔ N₁ := le_sup_right
  let u₂ : Fin a → (Fin c → TowerStage A t p (N ⊔ N₁)) := fun i ↦
    stageToStage A t p N₁ _ hN₁ (fun k ↦ z (Sum.inl (i, k)))
  let v₂ : Fin c → (Fin a → TowerStage A t p (N ⊔ N₁)) := fun k ↦
    stageToStage A t p N₁ _ hN₁ (fun i ↦ z (Sum.inr (k, i)))
  have hu₂ : ∀ i, stageToTower A t p _ (u₂ i) = u i := fun i ↦ by
    rw [show u₂ i = stageToStage A t p N₁ _ hN₁ (fun k ↦ z (Sum.inl (i, k))) from rfl,
      stageToTower_stageToStage]
    funext k
    rw [stageToTower_apply, hz]
    rfl
  have hv₂ : ∀ k, stageToTower A t p _ (v₂ k) = v' k := fun k ↦ by
    rw [show v₂ k = stageToStage A t p N₁ _ hN₁ (fun i ↦ z (Sum.inr (k, i))) from rfl,
      stageToTower_stageToStage]
    funext i
    rw [stageToTower_apply, hz]
    rfl
  let r₂ := stageToStage A t p N _ hN ∘ r
  let s₂ := stageToStage A t p N _ hN ∘ s
  have hs₂ : stageToTower A t p _ ∘ s₂ = stageToTower A t p N ∘ s :=
    funext fun l ↦ stageToTower_stageToStage A t p N _ hN (s l)
  -- 関係式と全射性の証人の族 `w`
  let w : Fin b ⊕ Fin c → (Fin c → TowerStage A t p (N ⊔ N₁)) :=
    Sum.elim (fun j ↦ ∑ i, r₂ j i • u₂ i) (fun k ↦ Pi.single k 1 - ∑ i, v₂ k i • u₂ i)
  have hw : ∀ x, stageToTower A t p _ (w x) ∈
      Submodule.span (Tower A t p) (Set.range (stageToTower A t p _ ∘ s₂)) := by
    rw [hs₂]
    rintro (j | k)
    · have h1 : stageToTower A t p _ (w (Sum.inl j)) =
          ∑ i, stageToTower A t p N (r j) i • u i := by
        rw [show w (Sum.inl j) = ∑ i, r₂ j i • u₂ i from rfl, map_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [stageToTower_smul, hu₂, ← stageToTower_apply,
          show r₂ j = stageToStage A t p N _ hN (r j) from rfl, stageToTower_stageToStage]
      have h2 : (Submodule.Quotient.mk (stageToTower A t p N (r j)) :
          (Fin a → Tower A t p) ⧸ Submodule.span (Tower A t p)
            (Set.range (stageToTower A t p N ∘ r))) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨j, rfl⟩)
      rw [h1, ← Submodule.Quotient.mk_eq_zero, ← hgmk, h2, map_zero]
    · have h1 : stageToTower A t p _ (w (Sum.inr k)) = Pi.single k 1 - ∑ i, v' k i • u i := by
        rw [show w (Sum.inr k) = Pi.single k 1 - ∑ i, v₂ k i • u₂ i from rfl, map_sub, map_sum,
          stageToTower_single, map_one]
        congr 1
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [stageToTower_smul, hu₂, ← stageToTower_apply, hv₂]
      rw [h1]
      refine (Submodule.Quotient.eq _).mp ?_
      rw [← hgmk, hv', hv]
  obtain ⟨N₃, h₂₃, hw₃⟩ := exists_stage_mem_span A t p _ s₂ w hw
  have hs₃ : stageToStage A t p _ N₃ h₂₃ ∘ s₂ = stageToStage A t p N N₃ (hN.trans h₂₃) ∘ s :=
    funext fun l ↦ stageToStage_stageToStage A t p N _ N₃ hN h₂₃ (s l)
  rw [hs₃] at hw₃
  let u₃ : Fin a → (Fin c → TowerStage A t p N₃) := fun i ↦ stageToStage A t p _ N₃ h₂₃ (u₂ i)
  -- `g'₀ : A_{N₃}^a → A_{N₃}^c / span (τ s)`、`e_i ↦ [u₃ i]`
  let g'₀ : (Fin a → TowerStage A t p N₃) →ₗ[TowerStage A t p N₃]
      ((Fin c → TowerStage A t p N₃) ⧸ Submodule.span (TowerStage A t p N₃)
        (Set.range (stageToStage A t p N N₃ (hN.trans h₂₃) ∘ s))) :=
    Fintype.linearCombination _ fun i ↦ Submodule.Quotient.mk (u₃ i)
  have hg'₀ : ∀ w₂ : Fin a → TowerStage A t p (N ⊔ N₁),
      g'₀ (stageToStage A t p _ N₃ h₂₃ w₂) =
        Submodule.Quotient.mk (stageToStage A t p _ N₃ h₂₃ (∑ i, w₂ i • u₂ i)) := by
    intro w₂
    rw [← Submodule.mkQ_apply]
    simp only [g'₀, Fintype.linearCombination_apply, stageToStage_apply, map_sum, map_smul,
      stageToStage_smul, u₃, Submodule.mkQ_apply]
  have hker : Submodule.span (TowerStage A t p N₃)
      (Set.range (stageToStage A t p N N₃ (hN.trans h₂₃) ∘ r)) ≤ LinearMap.ker g'₀ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, Function.comp_apply,
      ← stageToStage_stageToStage A t p N _ N₃ hN h₂₃, hg'₀, Submodule.Quotient.mk_eq_zero]
    exact hw₃ (Sum.inl j)
  refine ⟨N₃, hN.trans h₂₃, Submodule.liftQ _ g'₀ hker, ?_⟩
  -- 全射性：`[e_k]` が像に入る
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro y -
  obtain ⟨y₀, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [pi_eq_sum_univ' y₀, ← Submodule.mkQ_apply, map_sum]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ⟨Submodule.Quotient.mk (stageToStage A t p _ N₃ h₂₃ (v₂ k)), ?_⟩
  rw [Submodule.liftQ_apply, hg'₀, Submodule.mkQ_apply, Submodule.Quotient.eq]
  have := hw₃ (Sum.inr k)
  rw [show w (Sum.inr k) = Pi.single k 1 - ∑ i, v₂ k i • u₂ i from rfl, map_sub,
    stageToStage_single, map_one, ← neg_mem_iff, neg_sub] at this
  exact this

/-! ### 有限段の公式 -/

section formula

variable [Fact p.Prime]

/-- `L / p^{kh} = (p^{(N'−N)h} · (p^{(N−k)h} · L)) / p^{N'h}`（`k ≤ N ≤ N'`）。 -/
lemma div_stageRank_eq (k N N' : ℕ) (hk : k ≤ N) (hN : N ≤ N') (L : ℝ≥0∞) :
    L / (stageRank h p k : ℝ≥0∞) =
      ((stageRank h p (N' - N) : ℝ≥0∞) * ((stageRank h p (N - k) : ℝ≥0∞) * L)) /
        (stageRank h p N' : ℝ≥0∞) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hR : stageRank h p (N' - N) * stageRank h p (N - k) * stageRank h p k =
      stageRank h p N' := by
    simp only [stageRank]
    rw [← pow_add, ← pow_add, ← add_mul, ← add_mul]
    congr 2
    omega
  rw [← mul_assoc, ← hR]
  push_cast
  rw [ENNReal.mul_div_mul_left]
  · exact mul_ne_zero (by exact_mod_cast pow_ne_zero _ hp) (by exact_mod_cast pow_ne_zero _ hp)
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)

variable [IsLocalRing A] [IsNoetherianRing A] (ht : ∀ i, t i ∈ maximalIdeal A)

set_option linter.style.haveILetI false in
include ht in
/-- **降下の値の単調性**：有限長 `V`（段 `n`）、`W`（段 `m`）と `Λ` 線形な全射
`Λ ⊗_{A_m} W ↠ Λ ⊗_{A_n} V` があれば `ℓ(V)/p^{nh} ≤ ℓ(W)/p^{mh}`。 -/
lemma length_div_le_of_surjective (n m : ℕ) (V W : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] [AddCommGroup W] [Module (TowerStage A t p m) W]
    (hV : IsFiniteLength (TowerStage A t p n) V) (hW : IsFiniteLength (TowerStage A t p m) W)
    (f : Tower A t p ⊗[TowerStage A t p m] W →ₗ[Tower A t p] Tower A t p ⊗[TowerStage A t p n] V)
    (hf : Function.Surjective f) :
    (Module.length (TowerStage A t p n) V : ℝ≥0∞) / (stageRank h p n : ℝ≥0∞) ≤
      (Module.length (TowerStage A t p m) W : ℝ≥0∞) / (stageRank h p m : ℝ≥0∞) := by
  classical
  -- 共通の段 `N`
  have hnN : n ≤ n ⊔ m := le_sup_left
  have hmN : m ≤ n ⊔ m := le_sup_right
  letI := (towerMap A t p n _ hnN).toRingHom.toAlgebra
  letI := (towerMap A t p m _ hmN).toRingHom.toAlgebra
  haveI := isScalarTower_towerMap_tower A t p n _ hnN
  haveI := isScalarTower_towerMap_tower A t p m _ hmN
  haveI : IsNoetherian (TowerStage A t p n) V :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hV).1
  haveI : IsNoetherian (TowerStage A t p m) W :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hW).1
  haveI : Module.FinitePresentation (TowerStage A t p (n ⊔ m))
      (TowerStage A t p (n ⊔ m) ⊗[TowerStage A t p n] V) := Module.finitePresentation_of_finite _ _
  haveI : Module.FinitePresentation (TowerStage A t p (n ⊔ m))
      (TowerStage A t p (n ⊔ m) ⊗[TowerStage A t p m] W) := Module.finitePresentation_of_finite _ _
  -- `A_N ⊗ V`、`A_N ⊗ W` の有限表示
  obtain ⟨c, KV, eV, hKV⟩ := Module.FinitePresentation.exists_fin (TowerStage A t p (n ⊔ m))
    (TowerStage A t p (n ⊔ m) ⊗[TowerStage A t p n] V)
  obtain ⟨d, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hKV
  obtain ⟨a, KW, eW, hKW⟩ := Module.FinitePresentation.exists_fin (TowerStage A t p (n ⊔ m))
    (TowerStage A t p (n ⊔ m) ⊗[TowerStage A t p m] W)
  obtain ⟨b, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hKW
  -- `Λ` 上の同型 `Λ ⊗_{A_n} V ≃ Λ^c / span (ρ s)`、`Λ ⊗_{A_m} W ≃ Λ^a / span (ρ r)`
  let φV : Tower A t p ⊗[TowerStage A t p n] V ≃ₗ[Tower A t p]
      ((Fin c → Tower A t p) ⧸ Submodule.span (Tower A t p)
        (Set.range (stageToTower A t p (n ⊔ m) ∘ s))) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (TowerStage A t p n)
      (TowerStage A t p (n ⊔ m)) (Tower A t p) (Tower A t p) V).symm.trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Tower A t p) (Tower A t p))
        (eV.trans (Submodule.quotEquivOfEq _ _ hs.symm))).trans
        (baseChangeQuotEquiv (Tower A t p) s))
  let φW : Tower A t p ⊗[TowerStage A t p m] W ≃ₗ[Tower A t p]
      ((Fin a → Tower A t p) ⧸ Submodule.span (Tower A t p)
        (Set.range (stageToTower A t p (n ⊔ m) ∘ r))) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (TowerStage A t p m)
      (TowerStage A t p (n ⊔ m)) (Tower A t p) (Tower A t p) W).symm.trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Tower A t p) (Tower A t p))
        (eW.trans (Submodule.quotEquivOfEq _ _ hr.symm))).trans
        (baseChangeQuotEquiv (Tower A t p) r))
  -- 全射を段 `N'` に降ろす
  obtain ⟨N', hNN', g', hg'⟩ := exists_stage_surjective A t p (n ⊔ m) r s
    (φV.toLinearMap ∘ₗ f ∘ₗ φW.symm.toLinearMap)
    (φV.surjective.comp (hf.comp φW.symm.surjective))
  letI := (towerMap A t p (n ⊔ m) N' hNN').toRingHom.toAlgebra
  -- 段 `N'` での長さの比較
  have hle := Module.length_le_of_surjective g' hg'
  let ψV : ((Fin c → TowerStage A t p N') ⧸ Submodule.span (TowerStage A t p N')
      (Set.range (stageToStage A t p (n ⊔ m) N' hNN' ∘ s))) ≃ₗ[TowerStage A t p N']
      TowerStage A t p N' ⊗[TowerStage A t p (n ⊔ m)]
        (TowerStage A t p (n ⊔ m) ⊗[TowerStage A t p n] V) :=
    (baseChangeQuotEquiv (TowerStage A t p N') s).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
        ((Submodule.quotEquivOfEq _ _ hs).trans eV.symm))
  let ψW : ((Fin a → TowerStage A t p N') ⧸ Submodule.span (TowerStage A t p N')
      (Set.range (stageToStage A t p (n ⊔ m) N' hNN' ∘ r))) ≃ₗ[TowerStage A t p N']
      TowerStage A t p N' ⊗[TowerStage A t p (n ⊔ m)]
        (TowerStage A t p (n ⊔ m) ⊗[TowerStage A t p m] W) :=
    (baseChangeQuotEquiv (TowerStage A t p N') r).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
        ((Submodule.quotEquivOfEq _ _ hr).trans eW.symm))
  rw [ψV.length_eq, ψW.length_eq, length_tensor_towerMap A t p _ N' hNN' ht,
    length_tensor_towerMap A t p _ N' hNN' ht, length_tensor_towerMap A t p n _ hnN ht,
    length_tensor_towerMap A t p m _ hmN ht] at hle
  -- `ℝ≥0∞` へ移して `p^{N'h}` で割る
  have hle' := ENat.toENNReal_le.mpr hle
  simp only [ENat.toENNReal_mul, ENat.toENNReal_coe] at hle'
  rw [div_stageRank_eq p n (n ⊔ m) N' hnN hNN', div_stageRank_eq p m (n ⊔ m) N' hmN hNN']
  exact ENNReal.div_le_div_right hle' _

set_option linter.style.haveILetI false in
include ht in
/-- (S1) **有限段の公式（`λ*` の形）**：有限長の `A_n` 加群 `V` について
`λ*(Λ ⊗_{A_n} V) = ℓ_{A_n}(V) / p^{nh}`。`≤` は定義、`≥` は `length_div_le_of_surjective`。 -/
theorem fgLength_tensor (n : ℕ) (V : Type u) [AddCommGroup V] [Module (TowerStage A t p n) V]
    (hV : IsFiniteLength (TowerStage A t p n) V) :
    fgLength A t p (Tower A t p ⊗[TowerStage A t p n] V) =
      (Module.length (TowerStage A t p n) V : ℝ≥0∞) / (stageRank h p n : ℝ≥0∞) := by
  haveI : IsNoetherian (TowerStage A t p n) V :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hV).1
  haveI : Module.FinitePresentation (TowerStage A t p n) V :=
    Module.finitePresentation_of_finite _ _
  refine le_antisymm ?_ ?_
  · refine iInf_le_of_le (Tower A t p ⊗[TowerStage A t p n] V) (iInf_le_of_le inferInstance
      (iInf_le_of_le inferInstance (iInf_le_of_le inferInstance (iInf_le_of_le LinearMap.id
        (iInf_le_of_le Function.surjective_id ?_)))))
    exact iInf_le_of_le n (iInf_le_of_le V (iInf_le_of_le inferInstance (iInf_le_of_le inferInstance
      (iInf_le_of_le hV (iInf_le_of_le ⟨LinearEquiv.refl _ _⟩ le_rfl)))))
  · refine le_iInf fun P ↦ le_iInf fun i₁ ↦ le_iInf fun i₂ ↦ le_iInf fun hP ↦ le_iInf fun f ↦
      le_iInf fun hf ↦ ?_
    refine le_iInf fun m ↦ le_iInf fun W ↦ le_iInf fun j₁ ↦ le_iInf fun j₂ ↦ le_iInf fun hW ↦
      le_iInf fun ⟨eP⟩ ↦ ?_
    exact length_div_le_of_surjective A t p ht n m V W hV hW (f ∘ₗ eP.symm.toLinearMap)
      (hf.comp eP.symm.surjective)

end formula

/-! ## (2.2) -/

section formula2

variable [IsLocalRing A]

/-- `m_A A_n` 冪ねじれの `V` について `Λ ⊗_{A_n} V` は `m_A Λ` 冪ねじれ。 -/
lemma isPowTorsion_tower_tensor (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V]
    (hVt : IsPowTorsion ((maximalIdeal A).map (algebraMap A (TowerStage A t p n))) V) :
    IsPowTorsion (towerMaxIdeal A t p) (Tower A t p ⊗[TowerStage A t p n] V) := by
  obtain ⟨k, hk⟩ := hVt
  have := isPowTorsion_tensorProduct_of_isTorsionBySet (C := Tower A t p) _ V hk
  rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at this

variable [IsNoetherianRing A] [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)

set_option linter.style.haveILetI false in
include ht in
/-- **(2.2) 有限段の公式**：`λ_∞(Λ ⊗_{A_n} V) = ℓ_{A_n}(V) / p^{nh}`。(C1) と (S1) から。 -/
theorem towerLengthFun_tensor (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] (hV : IsFiniteLength (TowerStage A t p n) V)
    (hVt : IsPowTorsion ((maximalIdeal A).map (algebraMap A (TowerStage A t p n))) V) :
    towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V) =
      (Module.length (TowerStage A t p n) V : ℝ≥0∞) / (stageRank h p n : ℝ≥0∞) := by
  haveI : IsNoetherian (TowerStage A t p n) V :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hV).1
  rw [towerLengthFun_eq_fgLength A t p _ (isPowTorsion_tower_tensor A t p n V hVt),
    fgLength_tensor A t p ht n V hV]

end formula2

end Section2

end SerrePositivity

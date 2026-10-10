module

public import SerrePositivity.Paper.Lemma3_5.ConjugateSum
public import SerrePositivity.Paper.Lemma3_5.Normalized
public import SerrePositivity.Paper.Lemma3_5.Ordinary
public import SerrePositivity.CommutativeAlgebra.GeometricFiber
public import SerrePositivity.Inputs.Descent
public import SerrePositivity.PerfectComplex.K0
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.PerfectComplex.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Lemma 3.5（通常ノルム比較、論文 §3.4）

`notes/lemma-3-5.md` の方針どおり、仮定の重さで三つに分ける。仮定は構造体に束ねず、
節ごとの `variable` と `include` で直接与える。

- **3.5a**（節 a：`A` は Noether 局所環、`z` はパラメータ系 `hz`、`T` は `A` 上有限、
  `λ` は `m_A C` の冪で消える `C` 加群の正規化長さで `λ H_j(z^v; C) < ∞`（`hfin`））：
  `z` に台をもつ完全 `T` 複体 `P` について `χ_T(P)`、`χ_C(P)` は有限で、
  `K₀^{m_A}(T)` 上の準同型を定める。通常の長さ側は `length_homology_ne_top_of_radical` と
  `chiOrdHom_of_radical`（`Paper/Lemma3_5/Ordinary.lean`）、`λ` 側は `lemma_3_5a_lam_finite`
  （`Normalized.lean`、唯一の `sorry`）と `chiLamHom_of_finite`（`PerfectComplex/NormalizedEuler.lean`）。
  `lemma_3_5a` はこれらを論文の形に並べたもの。
- **3.5b**（節 b：さらに `A` は正則で `z` は正則パラメータ系（`hz'`、`hdim`））：`A` から来る類の上で
  `χ_T(Q ⊗_A T) = χ_C(Q ⊗_A T) = r · χ_A(Q)`。二つの等式は独立に示せるので分ける。
  普通の長さの側 `lemma_3_5b_ord` は `T` が局所環で剰余体が同じこと（`hres`）を使い、
  正規化長さの側 `lemma_3_5b_lam` は (3.9) の `v = 1`（`hkz`、`hq`）と `hfin` を使う。
  証明は `Paper/Lemma3_5/Ordinary.lean` と `Normalized.lean` の後半。
  `K₀^{m}(A)` が `[K(z)]` で生成されること（共通の入力）から、
  `K(z)` での値の比較に帰着する。
- **3.5c**（節 c：さらに剰余標数 `p > 0`、有限群 `G` が `A` 上 `T` に作用し、
  `Spec T → Spec A` は全射（`hsurj`）で幾何ファイバーで推移的（`htrans`））：
  共役和 `Σ_g χ_T(g^*P) = Σ_g χ_C(g^*P)`。証明は Theorem 3.1 の帰結 `theorem_3_1_K0`（層 2）と
  形式的補題 `conjSum_eq`、3.5a、3.5b による。

`lemma_3_5` はこれらの組み合わせ（有限性と共役和の一致）。

## 規約

- `χ_T` は `T` 上の長さで定義する（`chiOrd`）。剰余体が同じなので `A` 上の長さと一致する。
- `λ` の定義域は `m_A C` の冪で消える `C` 加群（論文どおり）。`Setup34` の `m_T C` とは
  `NormalizedLength.restrict` で移り合う。
- `A` が `ℤ_(p)` 代数であることは、局所環で剰余標数が `p` なら自動なので書かない。
- 節 b 以降は Lemma 3.4 と同じく `[IsRegularLocalRing A]` を仮定する（`IsLocalRing A`、
  `IsNoetherianRing A` はそこから来る）。そのため `[IsLocalRing A]` と `λ` は節ごとに置く。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal

namespace SerrePositivity

variable {A T C : Type u} [CommRing A] [CommRing T] [Algebra A T] [CommRing C]
  [Algebra T C] [Algebra A C] [IsScalarTower A T C] {e : ℕ} {z : Fin e → A}

/-- `z` が `m_A` を生成すれば `√(z) = m_A`。 -/
lemma radical_span_eq_maximalIdeal [IsLocalRing A]
    (hz' : Ideal.span (Set.range z) = maximalIdeal A) :
    (Ideal.span (Set.range z)).radical = maximalIdeal A := by
  rw [hz']
  exact (maximalIdeal.isMaximal A).isPrime.radical

/-! ## 3.5a：二つの評価の有限性と加法性 -/

section a

variable [IsLocalRing A] [IsNoetherianRing A] [Module.Finite A T]
  {lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C))}
  (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
  (hfin : ∀ (v j : ℕ), lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)

include hz hfin in
/-- **Lemma 3.5a**：`χ_T`、`χ_C` は有限で、`K₀^{m_A}(T)` 上の準同型を定める。 -/
theorem lemma_3_5a :
    (∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ), Module.length T (P.1.homology i) ≠ ⊤) ∧
      (∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
        lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤) ∧
      (∃ χ : K0Supported T (algebraMap A T ∘ z) →+ ℝ, ∀ P, χ (K0.mk P) = chiOrd P.1) ∧
      (∃ χ : K0Supported T (algebraMap A T ∘ z) →+ ℝ,
        ∀ P, χ (K0.mk P) = chiLam lam (algebraMap T C) P.1) :=
  ⟨length_homology_ne_top_of_radical hz, lemma_3_5a_lam_finite hz hfin,
    ⟨chiOrdHom_of_radical hz, chiOrdHom_of_radical_mk hz⟩,
    ⟨chiLamHom_of_finite hz (lemma_3_5a_lam_finite hz hfin),
      chiLamHom_of_finite_mk hz (lemma_3_5a_lam_finite hz hfin)⟩⟩

end a

/-! ## 3.5b：基底から来る複体の階数倍の公式 -/

section b

variable [IsRegularLocalRing A] [Module.Finite A T]
  {lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C))}
  (hz' : Ideal.span (Set.range z) = maximalIdeal A) (hdim : ringKrullDim A = e)
  (hkz : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0)
  (hq : lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T)
  (hfin : ∀ (v j : ℕ), lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)

include hz' hdim in
/-- 正則パラメータ系の Koszul 複体は `A/(z)` の分解（A1 から）。3.5b の両側が共通に使う。 -/
lemma isKoszulResolution_of_regular : IsKoszulResolution z :=
  isKoszulResolution_of_isWeaklyRegular z (isWeaklyRegular_of_span_eq_maximalIdeal A z hz' hdim)

include hz' hdim in
/-- **Lemma 3.5b、普通の長さの側** (3.14)：`χ_T(Q ⊗_A T) = r · χ_A(Q)`。
`λ` も (3.9) も使わない。`T` が局所環で剰余体が同じこと（`hres`）は、`T` 上の長さと
`A` 上の長さを一致させるためだけに使う。証明は `Paper/Lemma3_5/Ordinary.lean`。 -/
theorem lemma_3_5b_ord [IsLocalRing T]
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (hQ : IsPerfectSupported z Q) :
    chiOrd (baseChange (algebraMap A T) Q) = (Module.finrank A T : ℝ) * chiOrd Q :=
  lemma_3_5b_ord_of_koszul hz' (isKoszulResolution_of_regular hz' hdim) hres
    (koszulEulerChar_eq_finrank A T z hz' hdim) Q hQ

include hz' hdim hkz hq hfin in
/-- **Lemma 3.5b、正規化長さの側** (3.13)：`χ_C(Q ⊗_A T) = r · χ_A(Q)`。
`T` が局所環であることも剰余体が同じことも使わない。証明は `Paper/Lemma3_5/Normalized.lean`。 -/
theorem lemma_3_5b_lam (Q : CochainComplex (ModuleCat.{u} A) ℤ) (hQ : IsPerfectSupported z Q) :
    chiLam lam (algebraMap T C) (baseChange (algebraMap A T) Q) =
      (Module.finrank A T : ℝ) * chiOrd Q :=
  lemma_3_5b_lam_of_koszul hz' (isKoszulResolution_of_regular hz' hdim) hkz hq hfin Q hQ

include hz' hdim hkz hq hfin in
/-- **Lemma 3.5b**：`A` から来る類の上で `χ_T(Q ⊗_A T) = χ_C(Q ⊗_A T) = r · χ_A(Q)`。
`lemma_3_5b_ord` と `lemma_3_5b_lam` を並べたもの。 -/
theorem lemma_3_5b [IsLocalRing T]
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (hQ : IsPerfectSupported z Q) :
    chiOrd (baseChange (algebraMap A T) Q) = (Module.finrank A T : ℝ) * chiOrd Q ∧
      chiLam lam (algebraMap T C) (baseChange (algebraMap A T) Q) =
        (Module.finrank A T : ℝ) * chiOrd Q :=
  ⟨lemma_3_5b_ord hz' hdim hres Q hQ, lemma_3_5b_lam hz' hdim hkz hq hfin Q hQ⟩

/-! ## 3.5c：共役和の比較 -/

section c

variable [IsLocalRing T] (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p] (G : Type u) [Group G] [Fintype G]
  [MulSemiringAction G T] [SMulCommClass G A T]
  (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
  (htrans : IsGeometricallyTransitive A T G)

include hz' hdim hres hkz hq hfin p hsurj htrans in
/-- **Lemma 3.5c**：共役和での一致 (3.11)。証明は Theorem 3.1 の帰結
「`G` 不変な類は正の倍数が `K₀^{m_A}(A)` から来る」（層 2、`theorem_3_1_K0`）と、
3.5a（`χ_T`、`χ_C` が `K₀` 上の準同型）、3.5b（`K₀(A)` の像の上で一致）、
形式的補題 `conjSum_eq` による。 -/
theorem lemma_3_5c (P : PerfSupp T (algebraMap A T ∘ z)) :
    ∑ g : G, chiOrd (twist g P.1) = ∑ g : G, chiLam lam (algebraMap T C) (twist g P.1) := by
  have hz := radical_span_eq_maximalIdeal hz'
  have hfinite := lemma_3_5a_lam_finite (T := T) hz hfin
  -- 3.5a の準同型 `χ_T`、`χ_C` は `K₀(A)` の像の上で一致する（3.5b）
  have h1 : ∀ x, chiOrdHom_of_radical (T := T) hz (K0.map (algebraMap A T) x) =
      chiLamHom_of_finite hz hfinite (K0.map (algebraMap A T) x) := by
    intro x
    have : (chiOrdHom_of_radical (T := T) hz).comp (K0.map (algebraMap A T)) =
        (chiLamHom_of_finite hz hfinite).comp (K0.map (algebraMap A T)) :=
      K0.hom_ext fun Q ↦ by
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, K0.map_mk, chiOrdHom_of_radical_mk,
          chiLamHom_of_finite_mk, (lemma_3_5b hz' hdim hkz hq hfin hres Q.1 Q.2).1,
          (lemma_3_5b hz' hdim hkz hq hfin hres Q.1 Q.2).2]
    exact DFunLike.congr_fun this x
  -- Theorem 3.1 の帰結
  have h2 := theorem_3_1_K0 A T p z hz G hsurj htrans
  have key := conjSum_eq (K0.map (algebraMap A T)) _ _ h1 h2 (K0.mk P)
  simp only [K0.smul_mk, chiOrdHom_of_radical_mk, chiLamHom_of_finite_mk] at key
  -- `g ↦ g⁻¹` で和を取り直す
  rw [Fintype.sum_equiv (Equiv.inv G) (fun g ↦ chiOrd (twist g⁻¹ P.1))
      (fun g ↦ chiOrd (twist g P.1)) (fun _ ↦ rfl),
    Fintype.sum_equiv (Equiv.inv G) (fun g ↦ chiLam lam (algebraMap T C) (twist g⁻¹ P.1))
      (fun g ↦ chiLam lam (algebraMap T C) (twist g P.1)) (fun _ ↦ rfl)] at key
  exact key

include hz' hdim hres hkz hq hfin p hsurj htrans in
/-- **Lemma 3.5**（通常ノルム比較）：3.5a の有限性と 3.5c の共役和の一致をまとめたもの。 -/
theorem lemma_3_5 (P : PerfSupp T (algebraMap A T ∘ z)) :
    (∀ (g : G) (i : ℤ), Module.length T ((twist g P.1).homology i) ≠ ⊤) ∧
      (∀ (g : G) (i : ℤ),
        lam.len ((baseChange (algebraMap T C) (twist g P.1)).homology i) ≠ ⊤) ∧
      ∑ g : G, chiOrd (twist g P.1) = ∑ g : G, chiLam lam (algebraMap T C) (twist g P.1) :=
  have hz := radical_span_eq_maximalIdeal hz'
  ⟨fun g i ↦
      length_homology_ne_top_of_radical hz ⟨twist g P.1, isPerfectSupported_twist z g P.2⟩ i,
    fun g i ↦
      lemma_3_5a_lam_finite (T := T) hz hfin ⟨twist g P.1, isPerfectSupported_twist z g P.2⟩ i,
    lemma_3_5c hz' hdim hkz hq hfin hres p G hsurj htrans P⟩

end c

end b

end SerrePositivity

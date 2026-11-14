module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.PerfectComplex.Free.Euler
public import SerrePositivity.LengthAlgebra.KoszulFormula
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import SerrePositivity.PerfectComplex.KoszulGeneration
public import SerrePositivity.PerfectComplex.Free.K0
public import SerrePositivity.LengthAlgebra.Koszul
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.CommutativeAlgebra.Koszul.RegularEuler
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite
public import SerrePositivity.PerfectComplex.Perfect.FreeComparison
public import SerrePositivity.CommutativeAlgebra.GeometricFiber
public import SerrePositivity.Inputs.Descent
public import SerrePositivity.PerfectComplex.Free.Support
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # ノルム比較（論文 Lemma 3.5）

## 概要

`z` に台を持つ完全 `T` 複体 `P` の、通常の長さによる Euler 評価 `χ_T(P)` と正規化長さによる `χ_C(P) = χ_λ(P ⊗_T C)` を比べる。3.5a：両者は有限で `K₀^{m_A}(T)` 上の準同型を定める。3.5b：`A` から来る類の上で `χ_T(Q ⊗_A T) = χ_C(Q ⊗_A T) = rank_A T · χ_A(Q)`。3.5c：有限群 `G` が幾何ファイバーで推移的に作用するとき、共役和 `Σ_g χ_T(g^*P) = Σ_g χ_C(g^*P)` (3.11)。

## 方針

仮定の重さで節 a・b・c に分け、仮定は構造体に束ねず節ごとの `variable` と `include` で与える。3.5b は `K₀^{m}(A)` が `[K(z)]` で生成されることから `K(z)` での値の比較に帰着する。3.5c は共通の共役和比較 `LengthAlgebra.perfectEuler_conjSum_eq` に、Theorem 3.1 の帰結（`sorry`）を有限射影 K₀ に移した降下を渡す。

## 規約

`χ_T` は `T` 上の長さで定義する（剰余体が同じなので `A` 上の長さと一致）。`λ` の定義域は `m_A C` の冪で消える `C` 加群（論文どおり）。

## 使われ方

Paper/Section5/FirstComparison（`NormApplication`）。
-/

@[expose] public noncomputable section

universe u

section NormalizedPart

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T]
  [Algebra A T] [Module.Finite A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
  {e : ℕ} {z : Fin e → A} {lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C))}

omit [Module.Finite A T] in
/-- **Lemma 3.5a の正規化長さの有限性**：`√(z) = m_A` で、各冪 `v` と各次数 `j` について
`λ(H_j(z^v; C)) < ∞` なら、`z` に台をもつ完全 `T` 複体 `P` を `C` に係数拡大したホモロジーの `λ` は
有限。係数つき Koszul 複体を有限自由な項で評価し、零ホモトピーからの直和因子へ有限性を戻す。 -/
theorem lemma_3_5a_lam_finite
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfin : ∀ (v j : ℕ),
      lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)
    (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ) :
    lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤ := by
  have hs : IsSupported (algebraMap A C ∘ z) (baseChange (algebraMap T C) P.1) := by
    have h := isSupported_baseChange (algebraMap T C) P.2.supported
    have heq : algebraMap T C ∘ (algebraMap A T ∘ z) = algebraMap A C ∘ z := by
      funext j
      exact (IsScalarTower.algebraMap_apply A T C (z j)).symm
    rwa [heq] at h
  have hJ : (maximalIdeal A).map (algebraMap A C) ≤
      (Ideal.span (Set.range (algebraMap A C ∘ z))).radical := by
    have h := Ideal.map_radical_le (algebraMap A C) (I := Ideal.span (Set.range z))
    rwa [hz, Ideal.map_span, ← Set.range_comp] at h
  apply lambdaHomology_supported_projective_ne_top lam
    ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C))
    (algebraMap A C ∘ z) hJ ?_ (baseChange (algebraMap T C) P.1) ?_ ?_
    (baseChange_bounded (algebraMap T C) P.1 P.2.bounded) hs i
  · intro v _ q
    have heq : (fun j ↦ algebraMap A C (z j ^ v)) =
        (fun j ↦ (algebraMap A C (z j)) ^ v) := by ext j; exact map_pow _ _ _
    have h := LengthAlgebra.koszul_finite_of_homologySelf lam
      (fun j ↦ algebraMap A C (z j ^ v)) (hfin v) q
    rw [heq] at h
    exact h
  · intro q
    have := P.2.finite q
    exact finite_baseChange (algebraMap T C) (P.1.X q)
  · intro q
    have : Module.Free C ((baseChange (algebraMap T C) P.1).X q) := by
      have := P.2.free q
      exact free_baseChange (algebraMap T C) (P.1.X q)
    exact Module.Projective.of_free

end SerrePositivity


/-! ## Lemma 3.5b の入力の確認

二段階の係数変更を自然同型で一段にまとめる。
共通の基底公式の係数 `e_λ(z; C)` は、高次の零長さと第零商の計算から階数になる。
-/


open CategoryTheory Limits IsLocalRing

namespace SerrePositivity

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T]
  [Algebra A T] [Module.Finite A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
  {e : ℕ} {z : Fin e → A} {lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C))}

omit [Module.Finite A T] in
/-- **Lemma 3.5b、正規化長さの側**：共通の Koszul Euler 基底公式に、
高次の零長さと第零商の階数の計算を適用する。基底の Koszul 分解は入力として明示する。 -/
theorem lemma_3_5b_lam_of_koszul (hz' : Ideal.span (Set.range z) = maximalIdeal A)
    (hK : IsKoszulResolution z)
    (hkz : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0)
    (hq : lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T)
    (hfin : ∀ (v j : ℕ), lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (hQ : IsPerfectSupported z Q) :
    chiLam lam (algebraMap T C) (baseChange (algebraMap A T) Q) =
      (Module.finrank A T : ℝ) * chiOrd Q := by
  have hJ : (maximalIdeal A).map (algebraMap A C) ≤
      (Ideal.span (Set.range (algebraMap A C ∘ z))).radical := by
    rw [← hz', Ideal.map_span, ← Set.range_comp]
    exact Ideal.le_radical
  have hfinite : LengthAlgebra.KoszulFinite lam (algebraMap A C ∘ z) := by
    intro v _ q
    have heq : (fun j ↦ algebraMap A C (z j ^ v)) =
        (fun j ↦ (algebraMap A C (z j)) ^ v) := by ext j; exact map_pow _ _ _
    have h := LengthAlgebra.koszul_finite_of_homologySelf lam
      (fun j ↦ algebraMap A C (z j ^ v)) (hfin v) q
    rw [heq] at h
    exact h
  let i : baseChange (algebraMap T C) (baseChange (algebraMap A T) Q) ≅
      baseChange (algebraMap A C) Q :=
    (Functor.mapHomologicalComplexCompIso
      (ModuleCat.extendScalarsComp (algebraMap A T) (algebraMap T C)).symm (.up ℤ)).app Q ≪≫
        eqToIso (by rw [IsScalarTower.algebraMap_eq A T C])
  change lambdaEuler lam (baseChange (algebraMap T C) (baseChange (algebraMap A T) Q)) = _
  rw [lambdaEuler_eq_of_homotopyEquiv lam (HomotopyEquiv.ofIso i)]
  rw [LengthAlgebra.lambdaEuler_baseChange_eq_koszulEuler_mul (algebraMap A C) lam
    ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C)) z hJ hfinite hz' hK Q hQ,
    LengthAlgebra.koszulEuler_eq_length_quotient lam (algebraMap A C ∘ z) hkz,
    hq, ENNReal.toReal_natCast]

end SerrePositivity


end NormalizedPart

section OrdinaryPart

open IsLocalRing

namespace SerrePositivity

variable {A T : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T]
  [Algebra A T] [Module.Finite A T] {e : ℕ} {z : Fin e → A}
  (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)

include hz in
/-- **Lemma 3.5a の通常の長さの有限性**：`√(z) = m_A` なら、`z` に台をもつ完全 `T` 複体の各ホモロジーは
`T` 上有限長。`T` は `A` 上有限なので Noether、`T/(z)T` は Artin 環なので、
`homology_finiteLength_of_isPerfectSupported` が使える。 -/
theorem length_homology_ne_top_of_radical (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ) :
    Module.length T (P.1.homology i) ≠ ⊤ := by
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have := isArtinianRing_quotient_span_of_finite A T z hz
  exact Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported P.2 i)

/-- **Lemma 3.5a の通常の長さの加法性**：`√(z) = m_A` のとき、`χ_T` を `K₀^{(z)}(T)` 上の準同型にした
もの（`PerfectComplex/OrdinaryEuler.lean` の `chiOrdHom` に、`T` の Noether 性と `T/(z)T` の Artin 性を
供給する）。 -/
noncomputable def chiOrdHom_of_radical : K0Supported T (algebraMap A T ∘ z) →+ ℝ :=
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have := isArtinianRing_quotient_span_of_finite A T z hz
  chiOrdHom _

/-- `chiOrdHom_of_radical hz [P] = chiOrd P`。 -/
@[simp]
lemma chiOrdHom_of_radical_mk (P : PerfSupp T (algebraMap A T ∘ z)) :
    chiOrdHom_of_radical hz (K0.mk P) = chiOrd P.1 := by
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have := isArtinianRing_quotient_span_of_finite A T z hz
  exact chiOrdHom_mk _ _

end SerrePositivity


/-!
## Lemma 3.5b、通常の長さの側 (3.14)

`χ_T(Q ⊗_A T) = r · χ_A(Q)`（`r = rank_A T`、`χ_T` は `T` 上の長さ）。

共通の `LengthAlgebra.lambdaEuler_baseChange_eq_koszulEuler_mul` に通常長さを適用する。
この共通定理が基底上の Koszul 生成を扱うので、ここでは準同型の一致を再証明せず、
係数となる Koszul Euler 数を次の通り計算する。

- `χ_T(K(z) ⊗_A T) = χ^A(z; T)`（`chiOrd_baseChange_koszulComplex`）：`K(z) ⊗_A T ≅ K(z; T)` で、
  剰余体が同じ局所環 `T` 上では `T` 加群の `T` 上の長さと `A` 上の長さが一致する
  （`length_eq_of_common_residueField`）。
- `χ^A(z; T) = rank_A T` は仮定 `hχ` として受け取る。正則局所環では層 3a の入力
  `koszulEulerChar_eq_finrank`（証明済みの正則パラメータと有限自由分解からの導出）から出る。
- `χ_A(K(z)) = 1`（`chiOrd_koszulComplex`）。
-/


open CategoryTheory Limits IsLocalRing

namespace SerrePositivity

/-! ## Lemma 3.5b、普通の長さの側 -/

variable {A T : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T]
  [Algebra A T] [Module.Finite A T] [IsLocalRing T] {e : ℕ} {z : Fin e → A}

omit [IsLocalRing A] [IsNoetherianRing A] [Module.Finite A T] in
/-- 生成元での値：剰余体が同じなら `χ_T(K(z) ⊗_A T) = χ^A(z; T)`。`K(z) ⊗_A T ≅ K(z; T)`
（`baseChangeKoszulIso`）で、各ホモロジーの `T` 上の長さを `A` 上の長さに取り替える
（`length_restrictScalars_eq`）。 -/
theorem chiOrd_baseChange_koszulComplex
    (hres : Function.Surjective ((residue T).comp (algebraMap A T))) :
    chiOrd (baseChange (algebraMap A T) (koszulComplex z)) = koszulEulerChar A T z := by
  rw [chiOrd_eq_of_homotopyEquiv (HomotopyEquiv.ofIso (baseChangeKoszulIso (algebraMap A T) z))]
  unfold chiOrd koszulEulerChar
  congr 1
  funext i
  rw [length_restrictScalars_eq hres]

/-- **Lemma 3.5b、通常の長さの側**：共通の Koszul Euler 基底公式に、
通常長さの Koszul 有限性と、基底変更した Koszul Euler 数の階数の計算を適用する。 -/
theorem lemma_3_5b_ord_of_koszul (hz' : Ideal.span (Set.range z) = maximalIdeal A)
    (hK : IsKoszulResolution z)
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (hχ : koszulEulerChar A T z = Module.finrank A T)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (hQ : IsPerfectSupported z Q) :
    chiOrd (baseChange (algebraMap A T) Q) = (Module.finrank A T : ℝ) * chiOrd Q := by
  have hz : (Ideal.span (Set.range z)).radical = maximalIdeal A := by
    rw [hz']
    exact (maximalIdeal.isMaximal A).isPrime.radical
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have := isArtinianRing_quotient_span_of_finite A T z hz
  have h := LengthAlgebra.lambdaEuler_baseChange_eq_koszulEuler_mul
    (algebraMap A T) (NormalizedLength.ordinary T) Submodule.fg_bot z bot_le
    (fun v _ i ↦ ordinary_koszul_pow_finite (algebraMap A T ∘ z) v i) hz' hK Q hQ
  have hc : LengthAlgebra.koszulEuler (NormalizedLength.ordinary T) (algebraMap A T ∘ z) =
      (Module.finrank A T : ℝ) := by
    rw [ordinary_koszulEuler_eq_koszulEulerChar z hres, hχ]
  rw [hc, ← chiOrd_eq_lambdaEuler_ordinary] at h
  exact h

end SerrePositivity


end OrdinaryPart

section Lemma3_5Part

open IsLocalRing
open scoped ENNReal

namespace SerrePositivity

variable {A T C : Type u} [CommRing A] [CommRing T] [Algebra A T] [CommRing C]
  [Algebra T C] [Algebra A C] [IsScalarTower A T C] {e : ℕ} {z : Fin e → A}

/-- `z` が `m_A` を生成すれば `√(z) = m_A`（極大イデアルは素イデアルなので根基は自分自身）。節 b の
仮定 `hz'` から節 a の仮定 `hz` を作るのに使う。 -/
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
/-- **Lemma 3.5a**：`z` に台をもつ完全 `T` 複体 `P` について、ホモロジーの `T` 上の長さと、`C` に
係数拡大したホモロジーの `λ` はすべて有限で、`χ_T`、`χ_C` は `K₀^{m_A}(T)` 上の準同型を定める。
四つの主張を `Ordinary.lean`、`Normalized.lean`、`PerfectComplex/NormalizedEuler.lean` の結果から
並べたもの。 -/
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
/-- 正則局所環の正則パラメータ系 `z` の Koszul 複体は `A/(z) = k` の分解である。A1（`z` は弱正則列、
`CommutativeAlgebra/RegularLocalRing.lean`）と Koszul 複体の完全性
（`CommutativeAlgebra/Koszul/Resolution.lean`）
による。3.5b の両側が共通に使う。 -/
lemma isKoszulResolution_of_regular : IsKoszulResolution z :=
  isKoszulResolution_of_isWeaklyRegular z (isWeaklyRegular_of_span_eq_maximalIdeal A z hz' hdim)

include hz' hdim in
/-- **Lemma 3.5b、通常の長さの側** (3.14)：`z` に台をもつ完全 `A` 複体 `Q` について
`χ_T(Q ⊗_A T) = rank_A T · χ_A(Q)`。`λ` も (3.9) も使わない。`T` が局所環で剰余体が同じこと（`hres`）は
`T` 上の長さと `A` 上の長さを一致させるためだけに使い、`χ^A(z; T) = rank_A T` は層 3a の入力
`koszulEulerChar_eq_finrank` から得る。証明は `Paper/Section3/NormComparison.lean` の
`lemma_3_5b_ord_of_koszul`。 -/
theorem lemma_3_5b_ord [IsLocalRing T]
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (hQ : IsPerfectSupported z Q) :
    chiOrd (baseChange (algebraMap A T) Q) = (Module.finrank A T : ℝ) * chiOrd Q :=
  lemma_3_5b_ord_of_koszul hz' (isKoszulResolution_of_regular hz' hdim) hres
    (koszulEulerChar_eq_finrank A T z hz' hdim) Q hQ

include hz' hdim hkz hq hfin in
omit [Module.Finite A T] in
/-- **Lemma 3.5b、正規化長さの側** (3.13)：`z` に台をもつ完全 `A` 複体 `Q` について
`χ_C(Q ⊗_A T) = rank_A T · χ_A(Q)`。`T` が局所環であることも剰余体が同じことも使わず、(3.9) の
`v = 1`（`hkz`、`hq`）と有限性 `hfin` を使う。証明は `Paper/Section3/NormComparison.lean` の
`lemma_3_5b_lam_of_koszul`。 -/
theorem lemma_3_5b_lam (Q : CochainComplex (ModuleCat.{u} A) ℤ) (hQ : IsPerfectSupported z Q) :
    chiLam lam (algebraMap T C) (baseChange (algebraMap A T) Q) =
      (Module.finrank A T : ℝ) * chiOrd Q :=
  lemma_3_5b_lam_of_koszul hz' (isKoszulResolution_of_regular hz' hdim) hkz hq hfin Q hQ

include hz' hdim hkz hq hfin in
/-- **Lemma 3.5b**：`A` から来る類の上で `χ_T(Q ⊗_A T) = χ_C(Q ⊗_A T) = rank_A T · χ_A(Q)`。
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
/-- **Lemma 3.5c**：共役和の一致 (3.11)、`Σ_g χ_T(g^*P) = Σ_g χ_C(g^*P)`。

証明：perfect 複体の実現の比較定理 `LengthAlgebra.perfectEuler_conjSum_eq` を、係数環 `A → T` と
二つの長さ付き代数 `T → T`（通常の長さ）、`T → C`（`λ`）に適用する。入力は三つ。
(1) 二つの Koszul Euler 数の一致：通常の長さの側は `χ^A(z; T) = rank_A T`
（`chiOrd_baseChange_koszulComplex`、`koszulEulerChar_eq_finrank`）、`λ` の側は (3.9) の `v = 1`
（`hkz`、`hq`）から、どちらも `rank_A T`。(2) `λ` の Koszul 有限性（`hfin`）と台の条件。(3) 不変類の
降下：Theorem 3.1 の帰結 `theorem_3_1_K0`（層 2）を `perfectK0_descent_of_free` で有限射影 K₀ へ移す。
結論は有限射影 K₀ 上の等式なので、`freeToPerfectK0` で旧有限自由モデルの値 `chiOrd`、`chiLam` に
戻す。`g • [P] = [(g⁻¹)^*P]` なので、最後に `g ↦ g⁻¹` で和を取り直す。 -/
theorem lemma_3_5c (P : PerfSupp T (algebraMap A T ∘ z)) :
    ∑ g : G, chiOrd (twist g P.1) = ∑ g : G, chiLam lam (algebraMap T C) (twist g P.1) := by
  have hz := radical_span_eq_maximalIdeal hz'
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have := isArtinianRing_quotient_span_of_finite A T z hz
  have hK := isKoszulResolution_of_regular hz' hdim
  -- 二段階の係数変更 `A → T → C` を `A → C` に直す
  have heq : algebraMap T C ∘ algebraMap A T ∘ z = algebraMap A C ∘ z := by
    funext j
    exact (IsScalarTower.algebraMap_apply A T C (z j)).symm
  -- `λ` の側の台の条件と Koszul 有限性
  have hI : (maximalIdeal A).map (algebraMap A C) ≤
      (Ideal.span (Set.range (algebraMap T C ∘ algebraMap A T ∘ z))).radical := by
    rw [heq, ← hz', Ideal.map_span, ← Set.range_comp]
    exact Ideal.le_radical
  have hfinD : LengthAlgebra.KoszulFinite lam (algebraMap T C ∘ algebraMap A T ∘ z) := by
    rw [heq]
    intro v _ q
    have hpow : (fun j ↦ algebraMap A C (z j ^ v)) = (fun j ↦ (algebraMap A C (z j)) ^ v) := by
      ext j
      exact map_pow _ _ _
    have h := LengthAlgebra.koszul_finite_of_homologySelf lam
      (fun j ↦ algebraMap A C (z j ^ v)) (hfin v) q
    rw [hpow] at h
    exact h
  -- 基底公式の係数：二つの Koszul Euler 数はともに `rank_A T`
  have hc : LengthAlgebra.koszulEuler (NormalizedLength.ordinary T) (algebraMap A T ∘ z) =
      LengthAlgebra.koszulEuler lam (algebraMap T C ∘ algebraMap A T ∘ z) := by
    rw [heq, LengthAlgebra.koszulEuler_eq_length_quotient lam (algebraMap A C ∘ z) hkz, hq,
      ENNReal.toReal_natCast]
    rw [ordinary_koszulEuler_eq_koszulEulerChar z hres,
      koszulEulerChar_eq_finrank A T z hz' hdim]
  -- 比較定理の適用。降下は Theorem 3.1 の帰結を有限射影 K₀ へ移したもの
  have key := LengthAlgebra.perfectEuler_conjSum_eq (algebraMap A T) (RingHom.id T)
    (algebraMap T C) (NormalizedLength.ordinary T) lam Submodule.fg_bot
    ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C)) z bot_le hI
    (fun v _ i ↦ ordinary_koszul_pow_finite (algebraMap A T ∘ z) v i) hfinD hz' hK hc
    (perfectK0_descent_of_free z (theorem_3_1_K0 A T p z hz G hsurj htrans))
    (freeToPerfectK0 (K0.mk P))
  -- 有限射影 K₀ の類を旧有限自由モデルの値に戻す
  have hterm : ∀ g : G, g • freeToPerfectK0 (K0.mk P) = TriangulatedK0.mk
      (perfSuppHomotopyObj ⟨twist g⁻¹ P.1, isPerfectSupported_twist z g⁻¹ P.2⟩) := by
    intro g
    rw [← freeToPerfectK0_smul, K0.smul_mk, freeToPerfectK0_mk]
  have hord : ∀ g : G, LengthAlgebra.perfectBaseChangeEulerK0 (RingHom.id T)
      (NormalizedLength.ordinary T) Submodule.fg_bot (algebraMap A T ∘ z) bot_le
      (fun v _ i ↦ ordinary_koszul_pow_finite (algebraMap A T ∘ z) v i)
      (g • freeToPerfectK0 (K0.mk P)) = chiOrd (twist g⁻¹ P.1) := by
    intro g
    rw [hterm g]
    -- 恒等係数変更は評価を変えない。証明項の型に `⇑(RingHom.id T) ∘ w` が残るので `erw` で展開する
    erw [LengthAlgebra.perfectBaseChangeEulerK0_id, LengthAlgebra.perfectEulerK0_mk,
      LengthAlgebra.perfectEuler_eq_lambdaEuler, chiOrd_eq_lambdaEuler_ordinary]
    rfl
  have hlam : ∀ g : G, LengthAlgebra.perfectBaseChangeEulerK0 (algebraMap T C) lam
      ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C)) (algebraMap A T ∘ z) hI hfinD
      (g • freeToPerfectK0 (K0.mk P)) = chiLam lam (algebraMap T C) (twist g⁻¹ P.1) := by
    intro g
    rw [hterm g, LengthAlgebra.perfectBaseChangeEulerK0_free]
  simp only [hord, hlam] at key
  -- `g ↦ g⁻¹` で和を取り直す
  rw [Fintype.sum_equiv (Equiv.inv G) (fun g ↦ chiOrd (twist g⁻¹ P.1))
      (fun g ↦ chiOrd (twist g P.1)) (fun _ ↦ rfl),
    Fintype.sum_equiv (Equiv.inv G) (fun g ↦ chiLam lam (algebraMap T C) (twist g⁻¹ P.1))
      (fun g ↦ chiLam lam (algebraMap T C) (twist g P.1)) (fun _ ↦ rfl)] at key
  exact key

include hz' hdim hres hkz hq hfin p hsurj htrans in
/-- **Lemma 3.5**（通常ノルム比較）：`z` に台をもつ完全 `T` 複体 `P` の各共役 `g^*P` について、
ホモロジーの長さと係数拡大したホモロジーの `λ` が有限（3.5a を `g^*P` に適用）で、共役和が一致する
（3.5c）。§5 への入力の形（`Paper/Section5/FirstComparison.lean`）。 -/
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

end Lemma3_5Part

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Paper "Eq (3.13)"] _root_.SerrePositivity.lemma_3_5b_lam
attribute [cite Paper "Eq (3.14)"] _root_.SerrePositivity.lemma_3_5b_ord
attribute [cite Paper "Proof step 3.5a"] _root_.SerrePositivity.lemma_3_5a
attribute [cite Paper "Proof step 3.5b"] _root_.SerrePositivity.lemma_3_5b

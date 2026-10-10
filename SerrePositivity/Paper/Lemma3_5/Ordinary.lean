module

public import SerrePositivity.PerfectComplex.OrdinaryEuler
public import SerrePositivity.LengthAlgebra.KoszulFormula
public import SerrePositivity.LengthAlgebra.Ordinary
public import SerrePositivity.PerfectComplex.KoszulGeneration
public import SerrePositivity.PerfectComplex.K0
public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import SerrePositivity.Inputs.RegularLocalRing
public import SerrePositivity.CommutativeAlgebra.Koszul

/-!
# Lemma 3.5 の通常の長さの側

## 概要

Lemma 3.5a・3.5b のうち、通常の長さによる Euler 評価 `χ_T(P) = chiOrd P` に関する部分。正規化長さの
側は `Normalized.lean`。

- 前半（3.5a）：Noether 局所環 `A` 上有限な代数 `T` と、`√(z) = m_A` なる列 `z` に台をもつ完全 `T`
  複体について、ホモロジーが有限長（`length_homology_ne_top_of_radical`）で、`χ_T` が
  `K₀^{m_A}(T)` 上の準同型（`chiOrdHom_of_radical`）。`PerfectComplex/OrdinaryEuler.lean` の一般定理を
  使うために、`T/(z)T` が Artin 環であることを示す（`isArtinianRing_quotient_span_of_finite`：
  `A/(z)` が Artin 環で `T/(z)T` はその上有限）。この段階では `T` の局所性も正規化長さも要らない。
- 後半（3.5b）：階数倍の公式 (3.14) `χ_T(Q ⊗_A T) = r · χ_A(Q)`。剰余体が同じ局所環 `T` では
  `T` 上の長さと `A` 上の長さが一致することと、`K₀^{m}(A)` が `[K(z)]` で生成されることにより、
  `K(z)` での値 `χ_T(K(z) ⊗_A T) = χ^A(z; T)` の計算に帰着する。`χ^A(z; T) = rank_A T` は仮定として
  受け取り、論文の設定では一般の有限自由分解の Euler–Poincaré 公式と正則局所環の性質から導く。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

/-- Noether 局所環 `A` 上有限な代数 `T` と、`√(z) = m_A` なる列 `z` について、`T/(z)T` は Artin 環。
`A/(z)` は（`m_A` 準素イデアルによる商なので）Artin 環（`isArtinianRing_quotient_of_le_radical`）で、
`T/(z)T` はその上の有限生成加群だから。`T` の局所性は要らない。 -/
lemma isArtinianRing_quotient_span_of_finite (A T : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T] [Algebra A T]
    [Module.Finite A T] {e : ℕ} (z : Fin e → A)
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A) :
    IsArtinianRing (T ⧸ Ideal.span (Set.range (algebraMap A T ∘ z))) := by
  let I := Ideal.span (Set.range z)
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  have : IsArtinianRing (A ⧸ I) :=
    isArtinianRing_quotient_of_le_radical (maximalIdeal A) I (by rw [hz])
  have : Module.Finite A (T ⧸ I.map (algebraMap A T)) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A (I.map (algebraMap A T))).toLinearMap
      Ideal.Quotient.mk_surjective
  have : Module.Finite (A ⧸ I) (T ⧸ I.map (algebraMap A T)) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hI : I.map (algebraMap A T) =
      Ideal.span (Set.range (algebraMap A T ∘ z)) := by
    dsimp only [I]
    rw [Ideal.map_span, Set.range_comp]
  rw [← hI]
  exact IsArtinianRing.of_finite (A ⧸ I) (T ⧸ I.map (algebraMap A T))

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

end

/-!
## Lemma 3.5b、通常の長さの側 (3.14)

`χ_T(Q ⊗_A T) = r · χ_A(Q)`（`r = rank_A T`、`χ_T` は `T` 上の長さ）。

`Q ↦ χ_T(Q ⊗_A T)` と `Q ↦ r · χ_A(Q)` はどちらも `K₀^{m}(A)` 上の準同型（前者は 3.5a の
`chiOrdHom_of_radical` と基底変更 `K0.map` の合成、後者は `chiOrdHom` の `r` 倍）なので、`K₀^{m}(A)`
が `[K(z)]` で生成されること（`K0.hom_ext_koszul`）から、`K(z)` での値を比べれば足りる。

- `χ_T(K(z) ⊗_A T) = χ^A(z; T)`（`chiOrd_baseChange_koszulComplex`）：`K(z) ⊗_A T ≅ K(z; T)` で、
  剰余体が同じ局所環 `T` 上では `T` 加群の `T` 上の長さと `A` 上の長さが一致する
  （`length_eq_of_common_residueField`）。
- `χ^A(z; T) = rank_A T` は仮定 `hχ` として受け取る。正則局所環では層 3a の入力
  `koszulEulerChar_eq_finrank`（正則局所環の未証明の性質からの導出）から出る。
- `χ_A(K(z)) = 1`（`chiOrd_koszulComplex`）。
-/

@[expose] public section

universe u

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
    change lambdaEuler (NormalizedLength.ordinary T) _ = _
    rw [← chiOrd_eq_lambdaEuler_ordinary]
    rw [← chiOrd_eq_of_homotopyEquiv (HomotopyEquiv.ofIso (baseChangeKoszulIso (algebraMap A T) z))]
    rw [chiOrd_baseChange_koszulComplex hres, hχ]
  rw [hc, ← chiOrd_eq_lambdaEuler_ordinary] at h
  exact h

end SerrePositivity

end

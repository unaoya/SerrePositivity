module

public import SerrePositivity.PerfectComplex.OrdinaryEuler
public import SerrePositivity.PerfectComplex.KoszulGeneration
public import SerrePositivity.PerfectComplex.K0
public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import SerrePositivity.Inputs.RegularLocalRing
public import SerrePositivity.CommutativeAlgebra.Koszul

/-!
# 補題3.5の通常の長さによる評価

前半は補題3.5aの有限性と加法性を扱う。Noether 局所環 `A` 上有限な代数 `T` と、
`A` の閉点を定める列に台をもつ完全 `T` 複体に対し、通常の長さの一般定理を適用する。
この段階では `T` の局所性も正規化長さも必要ない。

後半は補題3.5bの階数倍の公式を扱う。剰余体が同じ局所環の間で長さを比較し、
`K₀` の Koszul 生成定理によって任意の複体の評価を Koszul 複体での評価に帰着する。
Koszul Euler 標数と階数の一致は仮定として受け取り、論文の設定では正則局所環の入力を使う。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

/-- Noether 局所環の閉点を定める準素イデアルを有限代数に拡大すると、商は Artin 環となる。
有限代数自身の局所性は仮定しない。 -/
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
/-- 補題3.5aの通常長の有限性。基底の閉点に台をもつ完全 `T` 複体の各ホモロジーは有限長である。
有限代数の商の Artin 性と、台つき完全複体の一般定理から導く。 -/
theorem length_homology_ne_top_of_radical (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ) :
    Module.length T (P.1.homology i) ≠ ⊤ := by
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have := isArtinianRing_quotient_span_of_finite A T z hz
  exact Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported P.2 i)

/-- 補題3.5aの通常長の加法性。`χ_T` を基底の閉点に台をもつ完全複体の `K₀` 上の準同型にする。 -/
noncomputable def chiOrdHom_of_radical : K0Supported T (algebraMap A T ∘ z) →+ ℝ :=
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have := isArtinianRing_quotient_span_of_finite A T z hz
  chiOrdHom _

/-- 補題3.5aの通常 Euler 準同型を複体の類で評価すると、元の Euler 評価に一致する。 -/
@[simp]
lemma chiOrdHom_of_radical_mk (P : PerfSupp T (algebraMap A T ∘ z)) :
    chiOrdHom_of_radical hz (K0.mk P) = chiOrd P.1 := by
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have := isArtinianRing_quotient_span_of_finite A T z hz
  exact chiOrdHom_mk _ _

end SerrePositivity

end

/-!
## Lemma 3.5b、普通の長さの側 (3.14)

`χ_T(Q ⊗_A T) = r · χ_A(Q)`（`r = rank_A T`、`χ_T` は `T` 上の長さ）。

`Q ↦ χ_T(Q ⊗_A T)` と `Q ↦ r · χ_A(Q)` はどちらも `K₀^{m}(A)` 上の準同型（前者は 3.5a の
`chiOrdHom_of_radical` と基底変更 `K0.map` の合成）なので、`K₀^{m}(A)` が `[K(z)]` で生成されること
（`K0.hom_ext_koszul`）から、`K(z)` での値を比べれば足りる。

- `χ_T(K(z) ⊗_A T) = χ^A(z; T)`：剰余体が同じ局所環 `T` 上では、`T` 加群の `T` 上の長さと
  `A` 上の長さは一致する（`length_eq_of_common_residueField`）。
- `χ^A(z; T) = rank_A T` は仮定 `hχ` として受け取る。正則局所環では層 3a の入力
  `koszulEulerChar_eq_finrank`（Serre の定理）から出る。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace SerrePositivity

/-! ## Lemma 3.5b、普通の長さの側 -/

variable {A T : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T]
  [Algebra A T] [Module.Finite A T] [IsLocalRing T] {e : ℕ} {z : Fin e → A}

omit [IsLocalRing A] [IsNoetherianRing A] [Module.Finite A T] in
/-- `K(z)` の値：`χ_T(K(z) ⊗_A T) = χ^A(z; T)`（剰余体が同じとき）。 -/
theorem chiOrd_baseChange_koszulComplex
    (hres : Function.Surjective ((residue T).comp (algebraMap A T))) :
    chiOrd (baseChange (algebraMap A T) (koszulComplex z)) = koszulEulerChar A T z := by
  rw [chiOrd_eq_of_homotopyEquiv (HomotopyEquiv.ofIso (baseChangeKoszulIso (algebraMap A T) z))]
  unfold chiOrd koszulEulerChar
  congr 1
  funext i
  rw [length_restrictScalars_eq hres]

/-- **Lemma 3.5b、普通の長さの側** (3.14)：`χ_T(Q ⊗_A T) = r · χ_A(Q)`。
`K(z)` が `A/(z)` の分解であること（`hK`）と `χ^A(z; T) = r`（`hχ`）を仮定する。
正則局所環なら前者は A1、後者は `koszulEulerChar_eq_finrank` から出る。 -/
theorem lemma_3_5b_ord_of_koszul (hz' : Ideal.span (Set.range z) = maximalIdeal A)
    (hK : IsKoszulResolution z)
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (hχ : koszulEulerChar A T z = Module.finrank A T)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (hQ : IsPerfectSupported z Q) :
    chiOrd (baseChange (algebraMap A T) Q) = (Module.finrank A T : ℝ) * chiOrd Q := by
  have hz : (Ideal.span (Set.range z)).radical = maximalIdeal A := by
    rw [hz']
    exact (maximalIdeal.isMaximal A).isPrime.radical
  have := isArtinianRing_quotient_span_of_eq hz'
  have key : (chiOrdHom_of_radical (T := T) hz).comp (K0.map (algebraMap A T)) =
      Module.finrank A T • chiOrdHom z :=
    K0.hom_ext_koszul hz' hK (by
      rw [AddMonoidHom.comp_apply, K0.map_mk, chiOrdHom_of_radical_mk, AddMonoidHom.smul_apply,
        chiOrdHom_mk]
      change chiOrd (baseChange (algebraMap A T) (koszulComplex z)) =
        Module.finrank A T • chiOrd (koszulComplex z)
      rw [chiOrd_baseChange_koszulComplex hres, hχ, chiOrd_koszulComplex hK hz', nsmul_eq_mul,
        mul_one])
  have h := DFunLike.congr_fun key (K0.mk ⟨Q, hQ⟩)
  rw [AddMonoidHom.comp_apply, K0.map_mk, chiOrdHom_of_radical_mk, AddMonoidHom.smul_apply,
    chiOrdHom_mk, nsmul_eq_mul] at h
  exact h

end SerrePositivity

end

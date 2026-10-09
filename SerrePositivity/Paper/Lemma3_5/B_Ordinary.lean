module

public import SerrePositivity.PerfectComplex.KoszulGeneration
public import SerrePositivity.PerfectComplex.K0Functor
public import SerrePositivity.CommutativeAlgebra.LengthComparison
public import SerrePositivity.Paper.Lemma3_5.A_Ordinary
public import SerrePositivity.Inputs.RegularLocalRing
public import SerrePositivity.CommutativeAlgebra.KoszulBaseChange

/-!
# Lemma 3.5b、普通の長さの側 (3.14)

`χ_T(Q ⊗_A T) = r · χ_A(Q)`（`r = rank_A T`、`χ_T` は `T` 上の長さ）。

`Q ↦ χ_T(Q ⊗_A T)` と `Q ↦ r · χ_A(Q)` はどちらも `K₀^{m}(A)` 上の準同型（前者は 3.5a の
`lemma_3_5a_ord` と基底変更 `K0.map` の合成）なので、`K₀^{m}(A)` が `[K(z)]` で生成されること
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
  obtain ⟨-, χT, hT⟩ := lemma_3_5a_ord A T z hz
  have key : χT.comp (K0.map (algebraMap A T)) = Module.finrank A T • chiOrdHom z :=
    K0.hom_ext_koszul hz' hK (by
      rw [AddMonoidHom.comp_apply, K0.map_mk, hT, AddMonoidHom.smul_apply, chiOrdHom_mk]
      change chiOrd (baseChange (algebraMap A T) (koszulComplex z)) =
        Module.finrank A T • chiOrd (koszulComplex z)
      rw [chiOrd_baseChange_koszulComplex hres, hχ, chiOrd_koszulComplex hK hz', nsmul_eq_mul,
        mul_one])
  have h := DFunLike.congr_fun key (K0.mk ⟨Q, hQ⟩)
  rw [AddMonoidHom.comp_apply, K0.map_mk, hT, AddMonoidHom.smul_apply, chiOrdHom_mk,
    nsmul_eq_mul] at h
  exact h

end SerrePositivity

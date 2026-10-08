module

public import SerrePositivity.Descent.Lemma35b.Generation
public import SerrePositivity.Descent.OrdinaryLength
public import SerrePositivity.Inputs.RegularLocalRing
public import SerrePositivity.KoszulBaseChange

/-!
# Lemma 3.5b、普通の長さの側 (3.14)

`χ_T(Q ⊗_A T) = r · χ_A(Q)`（`r = rank_A T`、`χ_T` は `T` 上の長さ）。

`Q ↦ χ_T(Q ⊗_A T)` と `Q ↦ r · χ_A(Q)` はどちらも `K₀^{m}(A)` 上の準同型（前者は 3.5a の
`lemma_3_5a_ord` と基底変更 `K0.map` の合成）なので、`K₀^{m}(A)` が `[K(z)]` で生成されること
（`K0.hom_ext_koszul`）から、`K(z)` での値を比べれば足りる。

- `χ_T(K(z) ⊗_A T) = χ^A(z; T)`：剰余体が同じ局所環 `T` 上では、`T` 加群の `T` 上の長さと
  `A` 上の長さは一致する（`length_eq_of_residue_surjective`）。
- `χ^A(z; T) = rank_A T` は仮定 `hχ` として受け取る。正則局所環では層 3a の入力
  `koszulEulerChar_eq_finrank`（Serre の定理）から出る。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace SerrePositivity

/-! ## 剰余体が同じときの長さの比較 -/

section length

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] [IsLocalRing T]
  (hres : Function.Surjective ((residue T).comp (algebraMap A T)))

include hres in
/-- 剰余体が同じなら、単純 `T` 加群は `A` 上でも単純。 -/
lemma isSimpleModule_of_residue_surjective (S : Type u) [AddCommGroup S] [Module T S]
    [Module A S] [IsScalarTower A T S] [IsSimpleModule T S] : IsSimpleModule A S := by
  obtain ⟨φ⟩ := IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := T) (M := S)
  -- `m_T` は `S` を消す
  have hkill : ∀ t ∈ maximalIdeal T, ∀ x : S, t • x = 0 := by
    intro t ht x
    apply φ.injective
    rw [map_smul, map_zero]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ x)
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ht
  -- `A` 部分加群は `T` 部分加群
  have hT : ∀ (p : Submodule A S) (t : T) (x : S), x ∈ p → t • x ∈ p := by
    intro p t x hx
    obtain ⟨a, ha⟩ := hres (residue T t)
    have hm : t - algebraMap A T a ∈ maximalIdeal T := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact ha.symm
    have : t • x = a • x := by
      rw [← sub_eq_zero, ← algebraMap_smul T a x, ← sub_smul]
      exact hkill _ hm x
    rw [this]
    exact p.smul_mem a hx
  have : Nontrivial S := IsSimpleModule.nontrivial T S
  refine { eq_bot_or_eq_top := fun p ↦ ?_ }
  let q : Submodule T S :=
    { carrier := p
      add_mem' := p.add_mem
      zero_mem' := p.zero_mem
      smul_mem' := fun t x hx ↦ hT p t x hx }
  rcases IsSimpleOrder.eq_bot_or_eq_top q with h | h
  · left
    ext x
    have := SetLike.ext_iff.mp h x
    simpa [q] using this
  · right
    ext x
    have := SetLike.ext_iff.mp h x
    simpa [q] using this

include hres in
/-- 剰余体が同じ局所環 `T` 上では、`T` 加群の `A` 上の長さと `T` 上の長さは一致する。 -/
theorem length_eq_of_residue_surjective (M : Type u) [AddCommGroup M] [Module T M]
    [Module A M] [IsScalarTower A T M] : Module.length A M = Module.length T M := by
  by_cases h : IsFiniteLength T M
  · suffices H : ∀ (M : Type u) [AddCommGroup M] [Module T M], IsFiniteLength T M →
        ∀ [Module A M] [IsScalarTower A T M], Module.length A M = Module.length T M from
      H M h
    intro M _ _ h
    induction h with
    | of_subsingleton => intro _ _; simp [Module.length_eq_zero]
    | @of_simple_quotient M _ _ N _ _ ih =>
      intro _ _
      have := isSimpleModule_of_residue_surjective hres (M ⧸ N)
      rw [Module.length_eq_succ_of_isSimpleModule_quotient N,
        Module.length_eq_add_of_exact (N.subtype.restrictScalars A) (N.mkQ.restrictScalars A)
          N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
        Module.length_eq_one A (M ⧸ N), ih]
  · have hT : Module.length T M = ⊤ := by
      by_contra hne
      exact h (Module.length_ne_top_iff.mp hne)
    rw [hT]
    by_contra hne
    have hA := Module.length_ne_top_iff.mp hne
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hA
    obtain ⟨_, _⟩ := hA
    have : IsNoetherian T M := isNoetherian_of_tower A inferInstance
    have : IsArtinian T M := isArtinian_of_tower A inferInstance
    exact h (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

include hres in
/-- 係数制限した `T` 加群の `A` 上の長さは `T` 上の長さに等しい。 -/
lemma length_restrictScalars_eq (M : ModuleCat.{u} T) :
    Module.length A ((ModuleCat.restrictScalars (algebraMap A T)).obj M) =
      Module.length T M := by
  let : Module A M := Module.compHom M (algebraMap A T)
  have : IsScalarTower A T M := ⟨fun a t m ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  exact length_eq_of_residue_surjective hres M

end length

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

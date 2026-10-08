module

public import SerrePositivity.Descent.Lemma35b.Generation
public import SerrePositivity.Descent.NormalizedLength
public import SerrePositivity.KoszulBaseChange

/-!
# Lemma 3.5b、正規化長さの側 (3.13)

`χ_C(Q ⊗_A T) = r · χ_A(Q)`（`r = rank_A T`）。

`Q ↦ χ_C(Q ⊗_A T)` と `Q ↦ r · χ_A(Q)` はどちらも `K₀^{m}(A)` 上の準同型（前者は 3.5a の
`lemma_3_5a_lam` と基底変更 `K0.map` の合成）なので、`K₀^{m}(A)` が `[K(z)]` で生成されること
（`K0.hom_ext_koszul`）から、`K(z)` での値を比べれば足りる。
`χ_C(K(z) ⊗_A T) = Σ (-1)^i λ H_i(z; C) = λ(C/zC) = r`（(3.9) の `v = 1`）、`χ_A(K(z)) = 1`。

論文は超 Tor スペクトル系列と Lemma 3.4 を使うが、ここでは生成元 `K(z)` での計算だけで済む
（Lemma 3.4 の `V = k` の場合にあたる）。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace SerrePositivity

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T]
  [Algebra A T] [Module.Finite A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
  {e : ℕ} {z : Fin e → A} {lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C))}

omit [IsNoetherianRing A] [Module.Finite A T] in
/-- `K(z)` の値：`χ_C(K(z) ⊗_A T) = λ(C/zC)`（正の次数の Koszul ホモロジーの `λ` が `0` のとき）。 -/
theorem chiLam_baseChange_koszulComplex
    (hkz : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0) :
    chiLam lam (algebraMap T C) (baseChange (algebraMap A T) (koszulComplex z)) =
      (lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z)))).toReal := by
  have hw : algebraMap T C ∘ (algebraMap A T ∘ z) = algebraMap A C ∘ z := by
    funext j
    exact (IsScalarTower.algebraMap_apply A T C (z j)).symm
  -- `(K(z) ⊗_A T) ⊗_T C ≅ K(z; C)`
  let i : baseChange (algebraMap T C) (baseChange (algebraMap A T) (koszulComplex z)) ≅
      koszulComplex (algebraMap A C ∘ z) :=
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap T C)).mapHomologicalComplex _).mapIso
      (baseChangeKoszulIso (algebraMap A T) z) ≪≫
      baseChangeKoszulIso (algebraMap T C) (algebraMap A T ∘ z) ≪≫ eqToIso (by rw [hw])
  have hlen : ∀ n : ℤ, lam.len
      ((baseChange (algebraMap T C) (baseChange (algebraMap A T) (koszulComplex z))).homology n) =
      lam.len ((koszulComplex (algebraMap A C ∘ z)).homology n) := fun n ↦
    lam.len_congr _ _ ((HomologicalComplex.homologyFunctor _ _ n).mapIso i).toLinearEquiv
  unfold chiLam
  simp_rw [hlen]
  rw [finsum_eq_single _ (0 : ℤ)]
  · rw [Int.negOnePow_zero, Units.val_one, Int.cast_one, one_mul,
      lam.len_congr _ _ (koszulComplex_homology_zero_equiv (algebraMap A C ∘ z)).some]
  · intro n hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
      have := hkz k (by omega)
      change lam.len (koszulHomologySelf (algebraMap A C ∘ z) k) = 0 at this
      rw [show lam.len ((koszulComplex (algebraMap A C ∘ z)).homology (-(k : ℤ))) = 0 from this]
      simp
    · have := ModuleCat.subsingleton_of_isZero
        (koszulComplex_isZero_homology_of_pos (algebraMap A C ∘ z) n hn)
      rw [lam.len_eq_zero_of_subsingleton]
      simp

/-- **Lemma 3.5b、正規化長さの側** (3.13)：`χ_C(Q ⊗_A T) = r · χ_A(Q)`。
`K(z)` が `A/(z)` の分解であること（`hK`）を仮定する。正則局所環なら A1 から出る。 -/
theorem lemma_3_5b_lam_of_koszul (hz' : Ideal.span (Set.range z) = maximalIdeal A)
    (hK : IsKoszulResolution z)
    (hkz : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0)
    (hq : lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T)
    (hfin : ∀ (v j : ℕ), lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) (hQ : IsPerfectSupported z Q) :
    chiLam lam (algebraMap T C) (baseChange (algebraMap A T) Q) =
      (Module.finrank A T : ℝ) * chiOrd Q := by
  have hz : (Ideal.span (Set.range z)).radical = maximalIdeal A := by
    rw [hz']
    exact (maximalIdeal.isMaximal A).isPrime.radical
  have := isArtinianRing_quotient_span_of_eq hz'
  obtain ⟨-, χC, hC⟩ := lemma_3_5a_lam (T := T) hz hfin
  have key : χC.comp (K0.map (algebraMap A T)) = Module.finrank A T • chiOrdHom z :=
    K0.hom_ext_koszul hz' hK (by
      rw [AddMonoidHom.comp_apply, K0.map_mk, hC, AddMonoidHom.smul_apply, chiOrdHom_mk]
      change chiLam lam (algebraMap T C) (baseChange (algebraMap A T) (koszulComplex z)) =
        Module.finrank A T • chiOrd (koszulComplex z)
      rw [chiLam_baseChange_koszulComplex hkz, hq, chiOrd_koszulComplex hK hz', nsmul_eq_mul,
        mul_one, ENNReal.toReal_natCast])
  have h := DFunLike.congr_fun key (K0.mk ⟨Q, hQ⟩)
  rw [AddMonoidHom.comp_apply, K0.map_mk, hC, AddMonoidHom.smul_apply, chiOrdHom_mk,
    nsmul_eq_mul] at h
  exact h

end SerrePositivity

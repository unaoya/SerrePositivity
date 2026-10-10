module

public import SerrePositivity.PerfectComplex.NormalizedEuler
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.PerfectComplex.KoszulGeneration
public import SerrePositivity.PerfectComplex.K0

/-!
# Lemma 3.5 の正規化長さの側

## 概要

Lemma 3.5a・3.5b のうち、正規化長さ `λ` による Euler 評価 `χ_C(P) = χ_λ(P ⊗_T C)` に関する部分。
通常の長さの側は `Ordinary.lean`。

- 前半 `lemma_3_5a_lam_finite`：Koszul ホモロジー `H_j(z^v; C)` の `λ` がすべて有限なら、`z` に台を
  もつ任意の完全 `T` 複体 `P` について `P ⊗_T C` のホモロジーの `λ` も有限。証明済み。
  この有限性には `T` が `A` 上有限であることは不要。冪ねじれ性と、`K₀` への降下
  （`chiLamHom_of_finite`）は `PerfectComplex/NormalizedEuler.lean` にある。
- 後半 `lemma_3_5b_lam_of_koszul`：階数倍の公式 (3.13) `χ_C(Q ⊗_A T) = r · χ_A(Q)`。前半の有限性に
  依存する。

## 前半の証明

台の条件から、`z_j^v • 𝟙 P` が零ホモトピックな共通の冪 `v` をとる。
`Q = P ⊗_T C` を係数とする `K(z^v; Q)` を反復写像錐 `koszulComplexOn` で構成する。
`Q` がその直和因子となることは `retractKoszulComplexOn` で証明済みであり、
`lambdaHomology_ne_top_of_koszulComplexOn` により有限性を `Q` へ戻せる。
この引き戻しと、`m_A C` の冪ねじれ性に必要な根基の包含は以下の証明へ接続済み。

`Q` の有限自由な項による有限フィルトレーションの評価は
`lambdaHomology_koszulComplexOn_ne_top` で与える。
各次数の項が有限自由なので、各層は `K(z^v; C)` の有限直和をシフトしたものとなり、
仮定された Koszul ホモロジーの有限性と長完全列の評価を反復して全体の有限性を得る。
ここでフィルトレーションをとる方向は係数複体 `Q` の次数である。
有限自由加群の基底分解とシフト同型も一般論として証明し、以下の定理へ接続している。
-/

@[expose] public section

universe u

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
  obtain ⟨v, hv⟩ := hs
  have hJ : (maximalIdeal A).map (algebraMap A C) ≤
      (Ideal.span (Set.range (fun k ↦ algebraMap A C (z k ^ v)))).radical := by
    have h := Ideal.map_radical_le (algebraMap A C) (I := Ideal.span (Set.range z))
    rw [hz, Ideal.map_span, ← Set.range_comp] at h
    apply h.trans
    apply Ideal.radical_le_radical_iff.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨v, ?_⟩
    change (algebraMap A C (z j)) ^ v ∈ _
    rw [← map_pow]
    exact Ideal.subset_span (Set.mem_range_self j)
  apply lambdaHomology_ne_top_of_koszulComplexOn lam
    ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C))
    (fun k ↦ algebraMap A C (z k ^ v)) hJ (baseChange (algebraMap T C) P.1)
    (fun j ↦ by simpa only [smulId, map_pow, Function.comp_apply] using hv j) i
  apply lambdaHomology_koszulComplexOn_ne_top lam
    ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C))
    (fun k ↦ algebraMap A C (z k ^ v)) hJ ?_ (baseChange (algebraMap T C) P.1) ?_ ?_
    (baseChange_bounded (algebraMap T C) P.1 P.2.bounded) i
  · intro j
    by_cases hj : 0 < j
    · have hz := koszulComplex_isZero_homology_of_pos (fun k ↦ algebraMap A C (z k ^ v)) j hj
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      rw [lam.len_eq_zero_of_subsingleton]
      exact ENNReal.zero_ne_top
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = -(k : ℤ) := ⟨(-j).toNat, by omega⟩
      exact hfin v k
  · intro j
    have := P.2.free j
    exact free_baseChange (algebraMap T C) (P.1.X j)
  · intro j
    have := P.2.finite j
    exact finite_baseChange (algebraMap T C) (P.1.X j)


end SerrePositivity

end

/-!
## Lemma 3.5b、正規化長さの側 (3.13)

`χ_C(Q ⊗_A T) = r · χ_A(Q)`（`r = rank_A T`）。

`Q ↦ χ_C(Q ⊗_A T)` と `Q ↦ r · χ_A(Q)` はどちらも `K₀^{m}(A)` 上の準同型（前者は 3.5a の
`chiLamHom_of_finite` と基底変更 `K0.map` の合成、後者は `chiOrdHom` の `r` 倍）なので、`K₀^{m}(A)`
が `[K(z)]` で生成されること（`K0.hom_ext_koszul`）から、`K(z)` での値を比べれば足りる：
`χ_C(K(z) ⊗_A T) = Σ (-1)^i λ(H_i(z; C)) = λ(C/zC) = r`（(3.9) の `v = 1`）と `χ_A(K(z)) = 1`
（`chiOrd_koszulComplex`）。

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
/-- 生成元での値：正次数の Koszul ホモロジーの `λ` が `0` なら `χ_C(K(z) ⊗_A T) = λ(C/zC)`。
`(K(z) ⊗_A T) ⊗_T C ≅ K(z; C)`（`baseChangeKoszulIso` を二回）なので、`χ_C` は `K(z; C)` のホモロジーの
`λ` の交代和。正の次数は項が零、負の次数は仮定 `hkz` で `0`、残る `0` 次は `H^0(K(z; C)) ≅ C/zC`。 -/
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

/-- **Lemma 3.5b、正規化長さの側** (3.13)：`z` が `m_A` を生成し、`K(z)` が `A/(z)` の分解（`hK`。
正則局所環なら A1 から出る）で、(3.9) の `v = 1`（`hkz`、`hq`）と有限性 `hfin` が成り立つなら、
`z` に台をもつ完全 `A` 複体 `Q` について `χ_C(Q ⊗_A T) = rank_A T · χ_A(Q)`。二つの準同型
`chiLamHom_of_finite ∘ K0.map` と `rank_A T • chiOrdHom` が `[K(z)]` で一致することを
`chiLam_baseChange_koszulComplex` と `chiOrd_koszulComplex` で確かめ、`K0.hom_ext_koszul` で
全体に延ばす。 -/
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
  have hfinite := lemma_3_5a_lam_finite (T := T) hz hfin
  have key : (chiLamHom_of_finite hz hfinite).comp (K0.map (algebraMap A T)) =
      Module.finrank A T • chiOrdHom z :=
    K0.hom_ext_koszul hz' hK (by
      rw [AddMonoidHom.comp_apply, K0.map_mk, chiLamHom_of_finite_mk, AddMonoidHom.smul_apply,
        chiOrdHom_mk]
      change chiLam lam (algebraMap T C) (baseChange (algebraMap A T) (koszulComplex z)) =
        Module.finrank A T • chiOrd (koszulComplex z)
      rw [chiLam_baseChange_koszulComplex hkz, hq, chiOrd_koszulComplex hK hz', nsmul_eq_mul,
        mul_one, ENNReal.toReal_natCast])
  have h := DFunLike.congr_fun key (K0.mk ⟨Q, hQ⟩)
  rw [AddMonoidHom.comp_apply, K0.map_mk, chiLamHom_of_finite_mk, AddMonoidHom.smul_apply,
    chiOrdHom_mk, nsmul_eq_mul] at h
  exact h

end SerrePositivity

end

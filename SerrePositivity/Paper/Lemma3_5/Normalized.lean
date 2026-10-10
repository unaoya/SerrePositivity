module

public import SerrePositivity.PerfectComplex.NormalizedEuler
public import SerrePositivity.LengthAlgebra.KoszulFormula
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.PerfectComplex.KoszulGeneration
public import SerrePositivity.PerfectComplex.K0

/-! # Lemma 3.5 の正規化長さの側

有限性は、有限射影項に対する共通の Koszul 長さ上界から得る。
階数倍公式は `LengthAlgebra.lambdaEuler_baseChange_eq_koszulEuler_mul` による
任意の Koszul Euler 数の基底公式の特殊例とする。

このファイルが供給する固有の入力は、基底のパラメータ、Koszul ホモロジーの有限性、
正の次数の零長さ、および第零商の長さと階数との一致である。
評価関手、Euler 加法性、K₀ への降下は共通層と有限射影版の実現を使う。
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

end

/-! ## Lemma 3.5b の入力の確認

二段階の係数変更を自然同型で一段にまとめる。
共通の基底公式の係数 `e_λ(z; C)` は、高次の零長さと第零商の計算から階数になる。
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

end

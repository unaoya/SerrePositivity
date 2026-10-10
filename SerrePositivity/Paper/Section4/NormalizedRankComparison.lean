module

public import SerrePositivity.Paper.Section4.OrdinaryRankComparison

/-!
# 冪等完備化前のランク商での正規化 Euler 比較

`A → T → C` のテンソル積の結合を使い、有限版3.5bを `A → C` の係数変更に書き直す。
その等式を支持つきランク商の `K₀` へ移す。冪等完備化後への拡張と、
`A → T → C` の商関手の合成そのものの同定は、ここでの主張には含めない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section4

open CategoryTheory IsLocalRing Filter
open SerrePositivity.Asymptotic

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing T] [Algebra A T] [Module.Finite A T]
  [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
  {e : ℕ} (z : Fin e → A)
  (lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C)))

omit [IsNoetherianRing A] in
/-- 基底の極大イデアルの像は、パラメータの像の根基に入る。 -/
lemma base_ideal_le_radical (hz : Ideal.span (Set.range z) = maximalIdeal A) :
    (maximalIdeal A).map (algebraMap A C) ≤
      (Ideal.span (Set.range (algebraMap A C ∘ z))).radical := by
  rw [← hz, Ideal.map_span, ← Set.range_comp]
  exact Ideal.le_radical

omit [IsNoetherianRing A] in
/-- 有限版3.5の有限性入力を、係数変更後の §4 のホモロジー評価の形にする。 -/
lemma base_koszul_pow_finite
    (hfin : ∀ v j : ℕ,
      lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)
    (v : ℕ) (i : ℤ) :
    lam.len ((koszulComplex (fun k ↦ (algebraMap A C (z k)) ^ v)).homology i) ≠ ⊤ := by
  have h := normalized_koszul_finite_of_homologySelf lam _ (hfin v) i
  have he : (fun k ↦ algebraMap A C (z k ^ v)) =
      (fun k ↦ (algebraMap A C (z k)) ^ v) := funext fun k ↦ map_pow _ _ _
  rwa [he] at h

/-- 二段階のテンソル積の同型を使い、有限版3.5bを直接の `A → C` に書き直す。 -/
lemma lambdaEuler_baseChange_eq_rank_mul
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hKoszul : IsKoszulResolution z)
    (hkz : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0)
    (hq : lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T)
    (hfin : ∀ v j : ℕ,
      lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : IsPerfectSupported z P) :
    lambdaEuler lam (baseChange (algebraMap A C) P) =
      (Module.finrank A T : ℝ) * chiOrd P := by
  let eF : ModuleCat.extendScalars (algebraMap A C) ≅
      ModuleCat.extendScalars (algebraMap A T) ⋙ ModuleCat.extendScalars (algebraMap T C) :=
    eqToIso (congrArg ModuleCat.extendScalars (IsScalarTower.algebraMap_eq A T C)) ≪≫
      ModuleCat.extendScalarsComp (algebraMap A T) (algebraMap T C)
  let eP : baseChange (algebraMap A C) P ≅
      baseChange (algebraMap T C) (baseChange (algebraMap A T) P) :=
    (NatIso.mapHomologicalComplex eF (.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app P).symm
  exact (lambdaEuler_eq_of_homotopyEquiv lam (HomotopyEquiv.ofIso eP)).trans
    (lemma_3_5b_lam_of_koszul hz hKoszul hkz hq hfin P hP)

/-- 正規化評価の階数倍公式を、冪等完備化前の支持つきランク商の `K₀` に移す。 -/
theorem normalizedRankEulerK0_changeRing [Nontrivial C]
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hKoszul : IsKoszulResolution z)
    (hkz : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0)
    (hq : lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T)
    (hfin : ∀ v j : ℕ,
      lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)
    {s : ℕ → ℕ} (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n) :
    (supportedRankEulerK0 lam ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C))
      (algebraMap A C ∘ z) (base_ideal_le_radical z hz)
      (fun v _ i ↦ base_koszul_pow_finite z lam hfin v i) U hU hs).comp
      (TriangulatedK0.map (supportedRankChangeRing (algebraMap A C) z)) =
        (Module.finrank A T : ℝ) •
          ordinaryRankEulerK0 z (isArtinianRing_quotient_span_of_eq hz) U hU hs := by
  dsimp only [ordinaryRankEulerK0]
  apply supportedRankEulerK0_changeRing
  intro P hP
  simpa only [← chiOrd_eq_lambdaEuler_ordinary] using
    lambdaEuler_baseChange_eq_rank_mul z lam hz hKoszul hkz hq hfin P hP

end SerrePositivity.Section4

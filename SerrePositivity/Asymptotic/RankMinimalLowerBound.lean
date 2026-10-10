module

public import SerrePositivity.Asymptotic.RankVanishing
public import SerrePositivity.Asymptotic.NormalizedLowerBound
public import SerrePositivity.PerfectComplex.MinimalLowerBound

/-! # ランク商の Euler 評価と極小性による下界

共通の反復錐の消滅・第零次同型と、実際の Koszul ホモロジーから構成した全射を接続する。
元の複体列の一様支持は要求せず、商での支持と零作用だけを使う。
-/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ} {J : Ideal R}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
  (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
  (h : scalarSupported z (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)))
  (v : ℕ) (hv : 0 < v)
  (hx : ∀ j, z j ^ v • 𝟙 (completedSequenceFunctor.obj (sequenceHomotopyObj K hK)) = 0)
  (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ z j ^ v) i) = 0)
  (hbound : ∀ t q, q < -(e : ℤ) ∨ 0 < q → IsZero (((evaluateComplex t).obj K).X q))

include hv hx hzero hbound

/-- 振幅 `[-e,0]` では、Euler 評価は実際の Koszul 第零ホモロジーの正規化極限。 -/
theorem completedRankEuler_eq_koszul_zero_limit :
    completedRankEuler lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) =
      normalizedLimit U s (fun t ↦ (lam.len
        ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology 0)).toReal) := by
  let X := completedComplexObj z K hK h
  have hz (q : ℤ) (hq : q ≠ 0) :
      IsZero ((completedRankHomology lam hfg z hJ hfin U hU hs q).obj X) :=
    completedRankHomology_vanishing lam hfg z hJ hfin U hU hs K hK h v hv hx hzero
      (-(e : ℤ)) 0 hbound q (by omega)
  obtain ⟨eq⟩ := completedRankHomology_koszul_zero_iso lam hfg z hJ hfin U hU hs
    K hK h v hx (fun q hq ↦ hz q (by omega))
  rw [completedRankEuler_eq_homologicalEuler,
    homologicalEuler_eq_length_zero (lengthQuotientValue lam s U hU hs)
      (completedRankHomology lam hfg z hJ hfin U hU hs 0)
      (fun Y hY ↦ (lengthQuotientValue_eq_zero_iff lam s U hU hs Y).mpr hY) X
      (fun q hq ↦ (hz q hq).of_iso
        ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q).app X))]
  calc
    _ = completedRankBetti lam hfg z hJ hfin U hU hs X 0 :=
      lengthQuotientValue_iso lam s U hU hs
        ((completedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs 0).app X)
    _ = completedRankBetti lam hfg z hJ hfin U hU hs
        (completedComplexObj z (sequenceKoszul (fun j ↦ z j ^ v) K)
          (sequenceKoszul_bounded _ K hK)
          (sequenceKoszul_map_supported completedSequenceFunctor z _ K hK h)) 0 :=
      lengthQuotientValue_iso lam s U hU hs eq
    _ = _ := by
      rw [completedRankBetti_complex z lam hfg hJ hfin U hU hs _ _
        (sequenceKoszul_pow_supported z v hv K hK)]
      apply congrArg (normalizedLimit U s)
      funext t
      exact congrArg ENNReal.toReal (lam.len_congr _ _
        (((HomologicalComplex.homologyFunctor _ _ 0).mapIso
          (evaluateSequenceKoszulIso (fun j ↦ z j ^ v) K t)).toLinearEquiv))

/-- 極小性の具体的な全射から得られる Euler 下界。
イデアルは極大イデアルに限らず、微分の座標とパラメータの冪を含めばよい。 -/
theorem completedRankEuler_minimal_lower_bound
    (I : Ideal R) (hI : IsPowTorsion J (R ⧸ I))
    (hmin : ∀ t (m : Fin ((K.X (-1)).rank t) → R) j, (K.d (-1) 0 t m) j ∈ I)
    (hzI : ∀ j, z j ^ v ∈ I) :
    (lam.len (R ⧸ I)).toReal * normalizedLimit U s (fun t ↦ ((K.X 0).rank t : ℝ)) ≤
      completedRankEuler lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) := by
  rw [completedRankEuler_eq_koszul_zero_limit lam hfg z hJ hfin U hU hs K hK h
    v hv hx hzero hbound]
  have hle := normalizedLimit_mono U hU s hs
    (fun t ↦ (lam.len (R ⧸ I)).toReal * ((K.X 0).rank t : ℝ))
    (fun t ↦ (lam.len
      ((koszulComplexOn (fun j ↦ z j ^ v) ((evaluateComplex t).obj K)).homology 0)).toReal)
    ((K.X 0).rank_isBigO.const_mul_left _)
    (sequenceKoszulHomology_isBigO lam hfg _ (le_radical_span_pow z hJ v)
      (hfin v hv) K hK 0) (Eventually.of_forall fun t ↦ ?_)
  · rw [normalizedLimit_const_mul U hU s hs _ (K.X 0).rank_isBigO] at hle
    exact hle
  · have hb := lambdaHomology_koszul_zero_minimal_lower_bound lam hfg
      (fun j ↦ z j ^ v) (le_radical_span_pow z hJ v) ((evaluateComplex t).obj K)
      (fun q hq ↦ hbound t q (Or.inr hq)) I hI ((K.X 0).rank t) (Iso.refl _)
      (hmin t) hzI
    have hr := ENNReal.toReal_mono
      (sequenceKoszulHomology_ne_top lam hfg _ (le_radical_span_pow z hJ v)
        (hfin v hv) K hK t 0) hb
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_comm] using hr

/-- 正の生成元数の極限と商の正の長さから Euler 正値性を得る。 -/
theorem completedRankEuler_pos_of_minimal
    (I : Ideal R) (hI : IsPowTorsion J (R ⧸ I))
    (hmin : ∀ t (m : Fin ((K.X (-1)).rank t) → R) j, (K.d (-1) 0 t m) j ∈ I)
    (hzI : ∀ j, z j ^ v ∈ I)
    (hlen : 0 < (lam.len (R ⧸ I)).toReal)
    (hrank : 0 < normalizedLimit U s (fun t ↦ ((K.X 0).rank t : ℝ))) :
    0 < completedRankEuler lam hfg z hJ hfin U hU hs (completedComplexObj z K hK h) :=
  (mul_pos hlen hrank).trans_le
    (completedRankEuler_minimal_lower_bound lam hfg z hJ hfin U hU hs K hK h
      v hv hx hzero hbound I hI hmin hzI)

end SerrePositivity.Asymptotic

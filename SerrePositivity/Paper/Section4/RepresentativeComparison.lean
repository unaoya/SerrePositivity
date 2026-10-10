module

public import SerrePositivity.Asymptotic.RankEulerComparison
public import SerrePositivity.Paper.Section4.KoszulInputs
public import SerrePositivity.Paper.Lemma3_5.Normalized

/-!
# 命題4.5の一様な代表複体に対する比較

有限版3.5bを各段に適用して、Euler 値の正規化超極限の比較を得る。
係数変更には実際の自由列の関手を用い、テンソル積との自然同型で有限版に接続する。
`supportedRankEuler_complex` により、ここでの超極限は支持つきランク商での評価である。
商の後に現れる一般の直和因子については、持ち上げの証明がなお必要である。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section4

open CategoryTheory Limits IsLocalRing Filter Asymptotics
open SerrePositivity.Asymptotic

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing T] [Algebra A T] [Module.Finite A T]
  {e : ℕ} {z : Fin e → A} {s : ℕ → ℕ}

/-- 一様に閉点に台をもつ自由複体列では、通常の Euler 値の列は `O(s)`。 -/
lemma ordinary_sequenceEuler_isBigO
    (hz : Ideal.span (Set.range z) = maximalIdeal A)
    (K : CochainComplex (FreeSequence A s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence A s) K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK)) :
    (fun n ↦ chiOrd ((evaluateComplex n).obj K)) =O[atTop] (fun n ↦ (s n : ℝ)) := by
  have := isArtinianRing_quotient_span_of_eq hz
  simpa only [chiOrd_eq_lambdaEuler_ordinary] using
    supportedSequenceEuler_isBigO (NormalizedLength.ordinary A) Submodule.fg_bot z bot_le
      (fun v _ i ↦ ordinary_koszul_pow_finite z v i) K hK hzK

/-- 命題4.5の通常の長さ側：一様な代表複体では有限版3.5bの超極限で従う。 -/
lemma ordinary_representative_comparison [IsLocalRing T]
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hKoszul : IsKoszulResolution z)
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (hχ : koszulEulerChar A T z = Module.finrank A T)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (K : CochainComplex (FreeSequence A s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence A s) K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK)) :
    normalizedLimit U s (fun n ↦ chiOrd ((evaluateComplex n).obj
      (((FreeSequence.changeRing (algebraMap A T)).mapHomologicalComplex (.up ℤ)).obj K))) =
      (Module.finrank A T : ℝ) *
        normalizedLimit U s (fun n ↦ chiOrd ((evaluateComplex n).obj K)) := by
  have hn (n : ℕ) : chiOrd ((evaluateComplex n).obj
      (((FreeSequence.changeRing (algebraMap A T)).mapHomologicalComplex (.up ℤ)).obj K)) =
      (Module.finrank A T : ℝ) * chiOrd ((evaluateComplex n).obj K) :=
    (chiOrd_eq_of_homotopyEquiv
      (HomotopyEquiv.ofIso (FreeSequence.evaluateComplexTensorIso (algebraMap A T) n K).symm)).trans
        (lemma_3_5b_ord_of_koszul hz hKoszul hres hχ _
          (evaluateComplex_isPerfectSupported z K hK hzK n))
  simp_rw [hn]
  exact normalizedLimit_const_mul U hU s hs _ (ordinary_sequenceEuler_isBigO hz K hK hzK) _

/-- 命題4.5の正規化長さ側：二回の係数変更を有限版3.5bのテンソル積と比較する。 -/
lemma normalized_representative_comparison
    [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
    (lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C)))
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hKoszul : IsKoszulResolution z)
    (hkz : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0)
    (hq : lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T)
    (hfin : ∀ v j : ℕ,
      lam.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (K : CochainComplex (FreeSequence A s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence A s) K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK)) :
    normalizedLimit U s (fun n ↦ lambdaEuler lam ((evaluateComplex n).obj
      (((FreeSequence.changeRing (algebraMap T C)).mapHomologicalComplex (.up ℤ)).obj
        (((FreeSequence.changeRing (algebraMap A T)).mapHomologicalComplex (.up ℤ)).obj K)))) =
      (Module.finrank A T : ℝ) *
        normalizedLimit U s (fun n ↦ chiOrd ((evaluateComplex n).obj K)) := by
  let KT := ((FreeSequence.changeRing (algebraMap A T)).mapHomologicalComplex (.up ℤ)).obj K
  have hn (n : ℕ) : lambdaEuler lam ((evaluateComplex n).obj
      (((FreeSequence.changeRing (algebraMap T C)).mapHomologicalComplex (.up ℤ)).obj KT)) =
      (Module.finrank A T : ℝ) * chiOrd ((evaluateComplex n).obj K) := by
    let e := (FreeSequence.evaluateComplexTensorIso (algebraMap T C) n KT).symm ≪≫
      ((ModuleCat.extendScalars (algebraMap T C)).mapHomologicalComplex (.up ℤ)).mapIso
        (FreeSequence.evaluateComplexTensorIso (algebraMap A T) n K).symm
    exact (lambdaEuler_eq_of_homotopyEquiv lam (HomotopyEquiv.ofIso e)).trans
      (lemma_3_5b_lam_of_koszul hz hKoszul hkz hq hfin _
        (evaluateComplex_isPerfectSupported z K hK hzK n))
  change normalizedLimit U s (fun n ↦ lambdaEuler lam ((evaluateComplex n).obj
    (((FreeSequence.changeRing (algebraMap T C)).mapHomologicalComplex (.up ℤ)).obj KT))) = _
  simp_rw [hn]
  exact normalizedLimit_const_mul U hU s hs _ (ordinary_sequenceEuler_isBigO hz K hK hzK) _

end SerrePositivity.Section4

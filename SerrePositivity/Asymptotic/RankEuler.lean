module
public import SerrePositivity.CategoryTheory.AlternatingSum

public import SerrePositivity.Asymptotic.CompletedHomology
public import SerrePositivity.Asymptotic.EulerLimit

/-!
# 支持つきランク商の対象上の Euler 評価

長さの Serre 商に値をもつホモロジー関手の有限な交代和を定義する。
実際の支持つき自由複体列の像では、各段の Euler 評価の正規化超極限に一致する。
ここでの対象上の評価と、三角関係で割った `K₀` 上の準同型は区別する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Filter
open scoped BigOperators

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ} {J : Ideal R}
  (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 支持つきランク商の対象上の Euler 評価。 -/
noncomputable def supportedRankEuler (P : SupportedSequenceRankQuotient (s := s) z) : ℝ :=
  ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * lengthQuotientValue lam s U hU hs
    ((supportedRankHomology lam hfg z hJ hfin U hU hs q).obj P)

/-- 冪等完備化した支持つきランク商の対象上の Euler 評価。 -/
noncomputable def completedSupportedEuler
    (P : Karoubi (SupportedSequenceRankQuotient (s := s) z)) : ℝ :=
  ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * lengthQuotientValue lam s U hU hs
    ((completedSupportedHomology lam hfg z hJ hfin U hU hs q).obj P)

/-- 商の冪等完備化で初めて台をもつ対象も含めた Euler 評価。 -/
noncomputable def completedRankEuler
    (P : (supportedCompletedRankQuotient (s := s) z).FullSubcategory) : ℝ :=
  completedSupportedEuler lam hfg z hJ hfin U hU hs
    ((supportedKaroubiEquivalence z).inverse.obj P)

/-- 完備化した評価の交代和は実際に有限支持である。 -/
lemma completedSupportedEuler_hasFiniteSupport
    (P : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    Function.HasFiniteSupport (fun q : ℤ ↦ ((q.negOnePow : ℤ) : ℝ) *
      lengthQuotientValue lam s U hU hs
        ((completedSupportedHomology lam hfg z hJ hfin U hU hs q).obj P)) := by
  obtain ⟨a, b, hab⟩ := completedSupportedHomology_bounded lam hfg z hJ hfin U hU hs P
  apply finiteSupport_of_bounded_zero _ a b
  intro q hq
  have hz := (lengthQuotientValue_eq_zero_iff lam s U hU hs _).mpr (hab q hq)
  simp only [hz, mul_zero]

/-- 冪等完備化前の対象では元の Euler 評価と一致する。 -/
lemma completedSupportedEuler_obj (P : SupportedSequenceRankQuotient (s := s) z) :
    completedSupportedEuler lam hfg z hJ hfin U hU hs ((toKaroubi _).obj P) =
      supportedRankEuler lam hfg z hJ hfin U hU hs P := by
  unfold completedSupportedEuler supportedRankEuler
  congr 1
  funext q
  congr 1
  exact lengthQuotientValue_iso lam s U hU hs
    ((completedSupportedHomologyFactors lam hfg z hJ hfin U hU hs q).app P)

/-- 商上の Euler 評価は同型で不変である。 -/
lemma supportedRankEuler_iso {P Q : SupportedSequenceRankQuotient (s := s) z} (i : P ≅ Q) :
    supportedRankEuler lam hfg z hJ hfin U hU hs P =
      supportedRankEuler lam hfg z hJ hfin U hU hs Q := by
  unfold supportedRankEuler
  congr 1
  funext q
  rw [lengthQuotientValue_iso lam s U hU hs
    ((supportedRankHomology lam hfg z hJ hfin U hU hs q).mapIso i)]

/-- 冪等完備化後の Euler 評価も同型で不変である。 -/
lemma completedSupportedEuler_iso
    {P Q : Karoubi (SupportedSequenceRankQuotient (s := s) z)} (i : P ≅ Q) :
    completedSupportedEuler lam hfg z hJ hfin U hU hs P =
      completedSupportedEuler lam hfg z hJ hfin U hU hs Q := by
  unfold completedSupportedEuler
  congr 1
  funext q
  rw [lengthQuotientValue_iso lam s U hU hs
    ((completedSupportedHomology lam hfg z hJ hfin U hU hs q).mapIso i)]

/-- 形式的直和因子の Euler 評価は、射影の誘導するホモロジーの像の長さの交代和である。 -/
lemma completedSupportedEuler_image
    (P : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    completedSupportedEuler lam hfg z hJ hfin U hU hs P =
      ∑ᶠ q : ℤ, ((q.negOnePow : ℤ) : ℝ) * lengthQuotientValue lam s U hU hs
        (Abelian.image ((supportedRankHomology lam hfg z hJ hfin U hU hs q).map P.p)) := by
  unfold completedSupportedEuler
  congr 1
  funext q
  congr 1
  exact lengthQuotientValue_iso lam s U hU hs
    (completedSupportedHomologyImageIso lam hfg z hJ hfin U hU hs P q)

/-- 実際の支持つき複体列のホモロジーの評価は、各段の長さの超極限である。 -/
lemma supportedRankHomology_length_complex
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK)) (q : ℤ) :
    lengthQuotientValue lam s U hU hs
      ((supportedRankHomology lam hfg z hJ hfin U hU hs q).obj
        ((rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q.obj
          ⟨sequenceHomotopyObj K hK, hzK⟩)) =
      normalizedLimit U s (fun n ↦ (lam.len (((evaluateComplex n).obj K).homology q)).toReal) := by
  refine (lengthQuotientValue_iso lam s U hU hs
    ((supportedRankHomologyFactors lam hfg z hJ hfin U hU hs q).app
      ⟨sequenceHomotopyObj K hK, hzK⟩)).trans ?_
  change sequenceLength lam s U _ = _
  unfold sequenceLength
  congr 1
  funext n
  exact congrArg ENNReal.toReal (lam.len_congr _ _
    (((moduleSequenceEvaluation n).mapIso (sequenceHomologyComplexIso K hK q)).toLinearEquiv))

/-- 実際の自由複体列の像の Euler 評価は、各段の Euler 評価の正規化超極限と一致する。 -/
lemma supportedRankEuler_complex
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK)) :
    supportedRankEuler lam hfg z hJ hfin U hU hs
      ((rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q.obj
        ⟨sequenceHomotopyObj K hK, hzK⟩) =
      normalizedLimit U s (fun n ↦ lambdaEuler lam ((evaluateComplex n).obj K)) := by
  unfold supportedRankEuler
  simp_rw [supportedRankHomology_length_complex lam hfg z hJ hfin U hU hs K hK hzK]
  obtain ⟨v, hv, hn⟩ := (sequence_supported_iff z K hK).mp hzK
  obtain ⟨a, b, ha, hb⟩ := hK
  symm
  apply normalizedLimit_lambdaEuler lam U hU s hs _ (Finset.Icc a b)
  · intro n q hq
    apply (FreeSequence.evaluation n).map_isZero
    simp only [Finset.mem_Icc] at hq
    by_cases hqa : q < a
    · exact K.isZero_of_isStrictlyGE a q hqa
    · exact K.isZero_of_isStrictlyLE b q (by omega)
  · intro q
    exact (complexHomologySequence_lengthBounded lam hfg (fun j ↦ z j ^ v)
      (le_radical_span_pow z hJ v) (hfin v hv) K ⟨a, b, ha, hb⟩ (fun n j ↦ hn j n) q).2.2

end SerrePositivity.Asymptotic

module

public import SerrePositivity.Asymptotic.RankQuotient
public import SerrePositivity.Asymptotic.NormalizedLimit
public import SerrePositivity.PerfectComplex.AsymptoticLengthBounds

/-!
# 自由列の圏に対する Koszul 長さ評価

具体的な自由列の複体から、既存の定量的 Koszul 評価が要求する
共通次数範囲と基底を取り出す。これにより長さの `O(s)`・`o(s)` 評価と
小さいランクの複体の正規化超極限の消滅を得る。
支持部分圏の商上へのホモロジー関手の降下はまだこの結論には含めない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter Asymptotics

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 有界性から、定量評価用の半開次数区間を列全体に共通して選べる。 -/
lemma sequenceComplex_uniform_interval (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P) :
    ∃ (a : ℤ) (w : ℕ), ∀ n i, (i < a ∨ a + w ≤ i) →
      IsZero (((evaluateComplex n).obj P).X i) := by
  obtain ⟨a, b, ha, hb⟩ := hP
  refine ⟨a, (b - a + 1).toNat, fun n i hi ↦ ?_⟩
  apply (FreeSequence.evaluation n).map_isZero
  rcases hi with hi | hi
  · exact P.isZero_of_isStrictlyGE a i hi
  · exact P.isZero_of_isStrictlyLE b i (by omega)

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (x : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
  (hfin : ∀ i, lam.len ((koszulComplex x).homology i) ≠ ⊤)

include hfg hJ hfin in
/-- 実数化する前の各段の Koszul ホモロジーの長さは有限である。 -/
lemma sequenceKoszulHomology_ne_top (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P) (n : ℕ) (q : ℤ) :
    lam.len ((koszulComplexOn x ((evaluateComplex n).obj P)).homology q) ≠ ⊤ := by
  obtain ⟨a, w, hbound⟩ := sequenceComplex_uniform_interval P hP
  exact ne_top_of_le_ne_top (ennreal_sum_nsmul_ne_top (Finset.range w)
    (fun j ↦ lam.len ((koszulComplex x).homology (q - (a + j)))) (fun _ _ ↦ hfin _)
    (fun j ↦ (P.X (a + j)).rank n))
    (lambdaHomology_koszulComplexOn_le_sum lam hfg x hJ a w
      (fun i ↦ (P.X i).rank n) ((evaluateComplex n).obj P) (hbound n)
      (fun _ _ _ ↦ ⟨Iso.refl _⟩) q)

include hfg hJ hfin in
/-- 共通有界な自由列に Koszul 関手を施すと、各次数の長さは `O(s)` となる。 -/
lemma sequenceKoszulHomology_isBigO (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P) (q : ℤ) :
    (fun n ↦ (lam.len ((koszulComplexOn x ((evaluateComplex n).obj P)).homology q)).toReal)
      =O[atTop] (fun n ↦ (s n : ℝ)) := by
  obtain ⟨a, w, hbound⟩ := sequenceComplex_uniform_interval P hP
  exact lambdaHomology_koszulComplexOn_isBigO lam hfg x hJ hfin a w
    (fun n i ↦ (P.X i).rank n) (fun n ↦ (evaluateComplex n).obj P) hbound
    (fun _ _ _ _ ↦ ⟨Iso.refl _⟩) _ (fun i _ _ ↦ (P.X i).rank_isBigO) q

include hfg hJ hfin in
/-- 小さいランクの共通有界複体では、Koszul ホモロジーの長さも通常の `o(s)` となる。 -/
lemma sequenceKoszulHomology_isLittleO (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : rankSmallComplex P) (q : ℤ) :
    (fun n ↦ (lam.len ((koszulComplexOn x ((evaluateComplex n).obj P)).homology q)).toReal)
      =o[atTop] (fun n ↦ (s n : ℝ)) := by
  obtain ⟨a, w, hbound⟩ := sequenceComplex_uniform_interval P hP.1
  exact lambdaHomology_koszulComplexOn_isLittleO lam hfg x hJ hfin a w
    (fun n i ↦ (P.X i).rank n) (fun n ↦ (evaluateComplex n).obj P) hbound
    (fun _ _ _ _ ↦ ⟨Iso.refl _⟩) _ (fun i _ _ ↦ hP.2 i) q

include hfg hJ hfin in
/-- 小さいランクの複体の Koszul ホモロジーは、正規化超極限で零になる。 -/
lemma sequenceKoszulHomology_normalizedLimit_eq_zero
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (P : CochainComplex (FreeSequence R s) ℤ) (hP : rankSmallComplex P) (q : ℤ) :
    normalizedLimit U s
      (fun n ↦ (lam.len ((koszulComplexOn x ((evaluateComplex n).obj P)).homology q)).toReal)
      = 0 :=
  normalizedLimit_eq_zero_of_isLittleO U hU s _
    (sequenceKoszulHomology_isLittleO lam hfg x hJ hfin P hP q)

end SerrePositivity.Asymptotic

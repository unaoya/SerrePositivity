module

public import SerrePositivity.Asymptotic.SequenceKoszulBounds
public import SerrePositivity.Asymptotic.SequenceSupport
public import SerrePositivity.Asymptotic.LengthQuotientValue

/-!
# 台をもつ自由列のホモロジーを長さの商へ送る

共通の零ホモトピーをもつ自由複体列について、ホモロジー列が長さで制限した
アーベル圏に属することを証明する。消去指数は列の添字にもホモロジー次数にも
依存しない。ランクが `o(s)` ならば、そのホモロジー列の像は長さの商で零になる。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter Asymptotics

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 自由列の複体の第 `q` ホモロジーを段ごとに並べた加群列。 -/
noncomputable def complexHomologySequence (P : CochainComplex (FreeSequence R s) ℤ)
    (q : ℤ) : ModuleSequence R :=
  Discrete.functor (fun n : ℕ ↦ ((evaluateComplex n).obj P).homology q)

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (x : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range x)).radical)

include hfg hJ in
/-- 共通の零ホモトピーから、ホモロジー列を一様に消すイデアル冪を得る。 -/
lemma complexHomologySequence_uniformlyPowTorsion
    (P : CochainComplex (FreeSequence R s) ℤ)
    (hnull : ∀ n j, Nonempty (Homotopy (smulId (x j) ((evaluateComplex n).obj P)) 0))
    (q : ℤ) : uniformlyPowTorsion J (complexHomologySequence P q) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ hfg
  refine ⟨k, fun n ↦ hk.trans ?_⟩
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  obtain ⟨H⟩ := hnull n j
  have h := H.homologyMap_eq q
  change HomologicalComplex.homologyMap (x j • 𝟙 _) q =
    HomologicalComplex.homologyMap 0 q at h
  rw [homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  change x j ∈ Module.annihilator R (((evaluateComplex n).obj P).homology q)
  rw [Module.mem_annihilator]
  intro m
  exact congrArg (fun f ↦ f.hom m) h

variable (hfin : ∀ i, lam.len ((koszulComplex x).homology i) ≠ ⊤)

include hfg hJ hfin in
/-- 零ホモトピーによる Koszul 直和因子表示から各段の有限性を得る。 -/
lemma complexHomologySequence_ne_top (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P)
    (hnull : ∀ n j, Nonempty (Homotopy (smulId (x j) ((evaluateComplex n).obj P)) 0))
    (n : ℕ) (q : ℤ) : lam.len ((complexHomologySequence P q).obj ⟨n⟩) ≠ ⊤ := by
  obtain ⟨a, w, hbound⟩ := sequenceComplex_uniform_interval P hP
  exact ne_top_of_le_ne_top (ennreal_sum_nsmul_ne_top (Finset.range w)
    (fun j ↦ lam.len ((koszulComplex x).homology (q - (a + j)))) (fun _ _ ↦ hfin _)
    (fun j ↦ (P.X (a + j)).rank n))
    (lambdaHomology_le_sum_of_nullHomotopies lam hfg x hJ a w
      (fun i ↦ (P.X i).rank n) ((evaluateComplex n).obj P) (hbound n)
      (fun _ _ _ ↦ ⟨Iso.refl _⟩) (hnull n) q)

include hfg hJ hfin in
/-- 台の一様な自由複体列のホモロジーは長さで制限したアーベル圏に入る。 -/
lemma complexHomologySequence_lengthBounded (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P)
    (hnull : ∀ n j, Nonempty (Homotopy (smulId (x j) ((evaluateComplex n).obj P)) 0))
    (q : ℤ) : lengthBoundedSequence lam s (complexHomologySequence P q) := by
  refine ⟨complexHomologySequence_uniformlyPowTorsion hfg x hJ P hnull q,
    fun n ↦ complexHomologySequence_ne_top lam hfg x hJ hfin P hP hnull n q, ?_⟩
  obtain ⟨a, w, hbound⟩ := sequenceComplex_uniform_interval P hP
  exact lambdaHomology_isBigO_of_nullHomotopies lam hfg x hJ hfin a w
    (fun n i ↦ (P.X i).rank n) (fun n ↦ (evaluateComplex n).obj P) hbound
    (fun _ _ _ _ ↦ ⟨Iso.refl _⟩) hnull _ (fun i _ _ ↦ (P.X i).rank_isBigO) q

include hfg hJ hfin in
/-- ランクの小さい支持つき列のホモロジーの長さは `o(s)` である。 -/
lemma complexHomologySequence_isLittleO (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : rankSmallComplex P)
    (hnull : ∀ n j, Nonempty (Homotopy (smulId (x j) ((evaluateComplex n).obj P)) 0))
    (q : ℤ) : (fun n ↦ (lam.len ((complexHomologySequence P q).obj ⟨n⟩)).toReal)
      =o[atTop] (fun n ↦ (s n : ℝ)) := by
  obtain ⟨a, w, hbound⟩ := sequenceComplex_uniform_interval P hP.1
  exact lambdaHomology_isLittleO_of_nullHomotopies lam hfg x hJ hfin a w
    (fun n i ↦ (P.X i).rank n) (fun n ↦ (evaluateComplex n).obj P) hbound
    (fun _ _ _ _ ↦ ⟨Iso.refl _⟩) hnull _ (fun i _ _ ↦ hP.2 i) q

/-- 有界支持つき列のホモロジーを長さで制限した圏の対象とみなす。 -/
noncomputable def boundedComplexHomologySequence (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P)
    (hnull : ∀ n j, Nonempty (Homotopy (smulId (x j) ((evaluateComplex n).obj P)) 0))
    (q : ℤ) : LengthBoundedSequence lam s :=
  ⟨complexHomologySequence P q,
    complexHomologySequence_lengthBounded lam hfg x hJ hfin P hP hnull q⟩

/-- ランクの小さい支持つき列のホモロジーは、長さの Serre 商で零となる。 -/
lemma boundedComplexHomologySequence_isZero
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)
    (P : CochainComplex (FreeSequence R s) ℤ) (hP : rankSmallComplex P)
    (hnull : ∀ n j, Nonempty (Homotopy (smulId (x j) ((evaluateComplex n).obj P)) 0))
    (q : ℤ) : IsZero ((lengthSerreQuotientFunctor lam s U hU hs).obj
      (boundedComplexHomologySequence lam hfg x hJ hfin P hP.1 hnull q)) := by
  rw [lengthSerreQuotient_isZero_iff]
  exact normalizedLimit_eq_zero_of_isLittleO U hU s _
    (complexHomologySequence_isLittleO lam hfg x hJ hfin P hP hnull q)

end SerrePositivity.Asymptotic

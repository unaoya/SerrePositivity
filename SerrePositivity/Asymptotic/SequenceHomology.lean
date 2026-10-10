module

public import SerrePositivity.Asymptotic.SequenceHomologyBounds
public import SerrePositivity.Asymptotic.SupportedRankQuotient
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor

/-!
# 支持つき自由列から長さで制限した加群列へのホモロジー関手

各段のホモロジーを離散関手として組み合わせる。台の共通指数を選び、
その冪の Koszul 複体による評価を適用して値域を長さで制限した圏に狭める。
この構成で要求する Koszul ホモロジーの有限性は明示的な入力である。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 共通有界ホモトピー圏の第 `n` 段の第 `q` ホモロジーへの関手。 -/
noncomputable abbrev sequenceHomologyEvaluation (q : ℤ) (n : ℕ) :
    SequenceHomotopy R s ⥤ ModuleCat.{u} R :=
  boundedHomotopyInclusion _ ⋙ (FreeSequence.evaluation n).mapHomotopyCategory (.up ℤ) ⋙
    HomotopyCategory.homologyFunctor _ _ q

/-- 共通有界自由列のホモロジーを加群列にまとめた関手。 -/
noncomputable def sequenceHomology (q : ℤ) : SequenceHomotopy R s ⥤ ModuleSequence R where
  obj P := Discrete.functor (fun n : ℕ ↦ (sequenceHomologyEvaluation q n).obj P)
  map f := Discrete.natTrans (fun n ↦ (sequenceHomologyEvaluation q n.as).map f)
  map_id P := by
    apply NatTrans.ext
    funext n
    exact CategoryTheory.Functor.map_id (sequenceHomologyEvaluation q n.as) P
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact CategoryTheory.Functor.map_comp (sequenceHomologyEvaluation q n.as) f g

instance sequenceHomology_additive (q : ℤ) : (sequenceHomology (R := R) (s := s) q).Additive where
  map_add {X Y} f g := by
    apply NatTrans.ext
    funext n
    exact Functor.map_add (sequenceHomologyEvaluation q n.as)

/-- 代表複体で計算したホモロジー列との比較同型。 -/
noncomputable def sequenceHomologyComplexIso (P : CochainComplex (FreeSequence R s) ℤ)
    (hP : strictlyBoundedComplex (FreeSequence R s) P) (q : ℤ) :
    (sequenceHomology q).obj (sequenceHomotopyObj P hP) ≅ complexHomologySequence P q :=
  Discrete.natIso (fun n ↦
    (HomotopyCategory.homologyFunctor _ _ q).mapIso
      (((FreeSequence.evaluation n.as).mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
    (HomotopyCategory.homologyFunctorFactors _ _ q).app ((evaluateComplex n.as).obj P))

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)

include hfg hJ hfin in
/-- 一様な台をもつ自由列のホモロジーは長さで制限した圏に属する。 -/
lemma sequenceHomology_lengthBounded (P : SequenceHomotopy R s)
    (hP : supportedSequence z P) (q : ℤ) :
    lengthBoundedSequence lam s ((sequenceHomology q).obj P) := by
  obtain ⟨Y, hY⟩ := P
  obtain ⟨K, rfl⟩ := Y.quotient_obj_surjective
  have hb := (boundedHomotopyProperty_quotient _ K).mp hY
  obtain ⟨v, hv, hn⟩ := (sequence_supported_iff z K hb).mp hP
  apply (lengthBoundedSequence lam s).prop_of_iso (sequenceHomologyComplexIso K hb q).symm
  exact complexHomologySequence_lengthBounded lam hfg (fun j ↦ z j ^ v)
    (le_radical_span_pow z hJ v) (hfin v hv) K hb (fun n j ↦ hn j n) q

/-- 支持つき自由列から長さで制限した加群列へのホモロジー関手。 -/
noncomputable def supportedSequenceHomology (q : ℤ) :
    (supportedSequence (s := s) z).FullSubcategory ⥤ LengthBoundedSequence lam s :=
  (lengthBoundedSequence lam s).lift ((supportedSequence z).ι ⋙ sequenceHomology q)
    (fun P ↦ sequenceHomology_lengthBounded lam hfg z hJ hfin P.obj P.property q)

instance supportedSequenceHomology_additive (q : ℤ) :
    (supportedSequenceHomology (s := s) lam hfg z hJ hfin q).Additive := by
  dsimp only [supportedSequenceHomology]
  infer_instance

/-- 支持つき自由列のホモロジーを長さの Serre 商に送る関手。 -/
noncomputable def supportedSequenceQuotientHomology
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n) (q : ℤ) :
    (supportedSequence (s := s) z).FullSubcategory ⥤ LengthSerreQuotient lam s U hU hs :=
  supportedSequenceHomology lam hfg z hJ hfin q ⋙ lengthSerreQuotientFunctor lam s U hU hs

end SerrePositivity.Asymptotic

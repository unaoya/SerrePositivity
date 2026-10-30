module

public import SerrePositivity.Asymptotic.RankHomologyShift
public import SerrePositivity.Asymptotic.CompletedHomology
public import SerrePositivity.CategoryTheory.Karoubi.Triangulated

/-! # ホモロジーのシフト比較の自然性と Karoubi 包絡への延長 -/

@[expose] public section

universe u

set_option synthInstance.maxSize 512

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Idempotents Filter
open CategoryTheory.Functor

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 自由列のホモロジーとシフトの比較は対象に自然。 -/
noncomputable def sequenceHomologyShiftNatIso (q : ℤ) :
    shiftFunctor (SequenceHomotopy R s) q ⋙ sequenceHomology 0 ≅ sequenceHomology q :=
  NatIso.ofComponents (fun P ↦ sequenceHomologyShiftIso P q) (fun {X Y} f ↦ by
    apply NatTrans.ext
    funext n
    let G := boundedHomotopyInclusion (FreeSequence R s) ⋙
      (FreeSequence.evaluation n.as).mapHomotopyCategory (.up ℤ)
    let H := HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
    let e := isoWhiskerRight (G.commShiftIso q) H ≪≫ isoWhiskerLeft G (H.isoShift q)
    exact e.hom.naturality f)

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 長さで制限したホモロジー関手のシフト比較。 -/
noncomputable def supportedSequenceHomologyShiftNatIso (q : ℤ) :
    shiftFunctor _ q ⋙ supportedSequenceHomology (s := s) lam hfg z hJ hfin 0 ≅
      supportedSequenceHomology lam hfg z hJ hfin q := by
  let i := (supportedSequence (s := s) z).ι
  let e := isoWhiskerRight (i.commShiftIso q) (sequenceHomology 0) ≪≫
    isoWhiskerLeft i (sequenceHomologyShiftNatIso q)
  exact NatIso.ofComponents (fun P ↦ ObjectProperty.isoMk _ (e.app P)) (fun f ↦ by
    apply ObjectProperty.hom_ext
    exact e.hom.naturality f)

/-- 長さの Serre 商に値をもつホモロジー関手のシフト比較。 -/
noncomputable def supportedSequenceQuotientHomologyShiftNatIso (q : ℤ) :
    shiftFunctor _ q ⋙ supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs 0 ≅
      supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q :=
  isoWhiskerRight (supportedSequenceHomologyShiftNatIso lam hfg z hJ hfin q)
    (lengthSerreQuotientFunctor lam s U hU hs)

variable [Nontrivial R]

/-- 商上のシフト比較を局所化の完全忠実な前合成から降ろす。 -/
noncomputable def supportedRankHomologyShiftNatIso (q : ℤ) :
    shiftFunctor _ q ⋙ supportedRankHomology lam hfg z hJ hfin U hU hs 0 ≅
      supportedRankHomology lam hfg z hJ hfin U hU hs q := by
  let W := (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW
  let L := W.Q
  let F := supportedRankHomology lam hfg z hJ hfin U hU hs 0
  let eq := isoWhiskerRight (L.commShiftIso q).symm F ≪≫
    isoWhiskerLeft (shiftFunctor _ q)
      (supportedRankHomologyFactors lam hfg z hJ hfin U hU hs 0) ≪≫
    supportedSequenceQuotientHomologyShiftNatIso lam hfg z hJ hfin U hU hs q ≪≫
    (supportedRankHomologyFactors lam hfg z hJ hfin U hU hs q).symm
  exact (Localization.fullyFaithfulWhiskeringLeft L W _).preimageIso eq

/-- Karoubi 包絡上でも次数別のホモロジーは第零ホモロジーのシフトである。 -/
noncomputable def completedSupportedHomologyShiftNatIso (q : ℤ) :
    shiftFunctor _ q ⋙ completedSupportedHomology lam hfg z hJ hfin U hU hs 0 ≅
      completedSupportedHomology lam hfg z hJ hfin U hU hs q := by
  let L := toKaroubi (SupportedSequenceRankQuotient (s := s) z)
  let F := completedSupportedHomology lam hfg z hJ hfin U hU hs 0
  let eq := isoWhiskerRight (L.commShiftIso q).symm F ≪≫
    isoWhiskerLeft (shiftFunctor _ q)
      (completedSupportedHomologyFactors lam hfg z hJ hfin U hU hs 0) ≪≫
    supportedRankHomologyShiftNatIso lam hfg z hJ hfin U hU hs q ≪≫
    (completedSupportedHomologyFactors lam hfg z hJ hfin U hU hs q).symm
  exact ((whiskeringLeft _ _ _).obj L).preimageIso eq

instance completedSupportedHomology_isHomological (q : ℤ) :
    (completedSupportedHomology lam hfg z hJ hfin U hU hs q).IsHomological := by
  dsimp only [completedSupportedHomology]
  infer_instance

end SerrePositivity.Asymptotic

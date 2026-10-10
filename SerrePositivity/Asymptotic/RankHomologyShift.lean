module

public import SerrePositivity.Asymptotic.SequenceHomologyLocalization
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# ランク商のホモロジー評価とシフト

第 `q` ホモロジーと、`q` シフトした対象の第零ホモロジーを比較する。
支持つき自由列上での比較を、商関手との自然同型を通じてランク商へ移す。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits Filter

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 自由列のホモロジー評価とシフトの比較。 -/
noncomputable def sequenceHomologyShiftIso (P : SequenceHomotopy R s) (q : ℤ) :
    (sequenceHomology 0).obj (P⟦q⟧) ≅ (sequenceHomology q).obj P :=
  Discrete.natIso (fun n ↦ by
    let G := boundedHomotopyInclusion (FreeSequence R s) ⋙
      (FreeSequence.evaluation n.as).mapHomotopyCategory (.up ℤ)
    let H := HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
    exact H.mapIso ((G.commShiftIso q).app P) ≪≫ (H.isoShift q).app (G.obj P))

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)
  (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

/-- 長さの商に値をもつ支持つき列のホモロジーとシフトの比較。 -/
noncomputable def supportedSequenceQuotientHomologyShiftIso
    (P : (supportedSequence (s := s) z).FullSubcategory) (q : ℤ) :
    (supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs 0).obj (P⟦q⟧) ≅
      (supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).obj P :=
  (lengthSerreQuotientFunctor lam s U hU hs).mapIso (ObjectProperty.isoMk _
    ((sequenceHomology 0).mapIso (((supportedSequence z).ι.commShiftIso q).app P) ≪≫
      sequenceHomologyShiftIso P.obj q))

variable [Nontrivial R]

/-- 支持つきランク商上のホモロジーとシフトの比較。 -/
noncomputable def supportedRankHomologyShiftIso
    (P : SupportedSequenceRankQuotient (s := s) z) (q : ℤ) :
    (supportedRankHomology lam hfg z hJ hfin U hU hs 0).obj (P⟦q⟧) ≅
      (supportedRankHomology lam hfg z hJ hfin U hU hs q).obj P := by
  let L := (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
  let := Localization.essSurj L (rankSmallBounded.inverseImage (supportedSequence z).ι).trW
  let X := L.objPreimage P
  let i := L.objObjPreimageIso P
  let H₀ := supportedRankHomology lam hfg z hJ hfin U hU hs 0
  let Hq := supportedRankHomology lam hfg z hJ hfin U hU hs q
  exact H₀.mapIso ((shiftFunctor _ q).mapIso i).symm ≪≫
    H₀.mapIso ((L.commShiftIso q).app X).symm ≪≫
    (supportedRankHomologyFactors lam hfg z hJ hfin U hU hs 0).app (X⟦q⟧) ≪≫
    supportedSequenceQuotientHomologyShiftIso lam hfg z hJ hfin U hU hs X q ≪≫
    ((supportedRankHomologyFactors lam hfg z hJ hfin U hU hs q).app X).symm ≪≫ Hq.mapIso i

end SerrePositivity.Asymptotic

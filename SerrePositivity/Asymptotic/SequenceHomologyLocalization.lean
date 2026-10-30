module

public import SerrePositivity.Asymptotic.SequenceHomology
public import SerrePositivity.CategoryTheory.Triangulated.VerdierLift

/-!
# ホモロジー評価の支持つきランク商への降下

加群列へのホモロジー関手の完全性を各段で確認する。
小さいランクの対象を長さの商で零に送ることから、Verdier 商の分母を反転する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Filter

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 加群列の完全性は各段の完全性から従う。 -/
lemma moduleSequence_exact_of_eval (S : ShortComplex (ModuleSequence R))
    (hS : ∀ n, (S.map (moduleSequenceEvaluation n)).Exact) : S.Exact := by
  rw [S.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext n
  have hn : IsZero ((moduleSequenceEvaluation n.as).obj S.homology) :=
    ((S.map (moduleSequenceEvaluation n.as)).exact_iff_isZero_homology.mp (hS n.as)).of_iso
      (S.mapHomologyIso (moduleSequenceEvaluation n.as)).symm
  exact hn.eq_of_src _ _

instance sequenceHomology_isHomological (q : ℤ) :
    (sequenceHomology (R := R) (s := s) q).IsHomological where
  exact T hT := by
    apply moduleSequence_exact_of_eval
    intro n
    exact (sequenceHomologyEvaluation q n).map_distinguished_exact T hT

variable {J : Ideal R} (lam : NormalizedLength R J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R) (hJ : J ≤ (Ideal.span (Set.range z)).radical)
  (hfin : ∀ v : ℕ, 0 < v → ∀ i, lam.len ((koszulComplex (fun j ↦ z j ^ v)).homology i) ≠ ⊤)

instance supportedSequenceHomology_isHomological (q : ℤ) :
    (supportedSequenceHomology (s := s) lam hfg z hJ hfin q).IsHomological where
  exact T hT := by
    apply (ShortComplex.exact_map_iff_of_faithful _ (lengthBoundedSequence lam s).ι).mp
    exact ((supportedSequence (s := s) z).ι ⋙ sequenceHomology q).map_distinguished_exact T hT

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ n, 0 < s n)

instance supportedSequenceQuotientHomology_additive (q : ℤ) :
    (supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).Additive := by
  dsimp only [supportedSequenceQuotientHomology]
  infer_instance

instance supportedSequenceQuotientHomology_isHomological (q : ℤ) :
    (supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).IsHomological where
  exact T hT :=
    ((supportedSequenceHomology lam hfg z hJ hfin q).map_distinguished_exact T hT).map
      (lengthSerreQuotientFunctor lam s U hU hs)

/-- 支持つき複体の小さいランク条件は、ホモロジー評価の消滅を与える。 -/
lemma supportedSequenceQuotientHomology_smallComplex
    (K : CochainComplex (FreeSequence R s) ℤ) (hK : rankSmallComplex K)
    (hzK : supportedSequence z (sequenceHomotopyObj K hK.1)) (q : ℤ) :
    IsZero ((supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).obj
      ⟨sequenceHomotopyObj K hK.1, hzK⟩) := by
  obtain ⟨v, hv, hn⟩ := (sequence_supported_iff z K hK.1).mp hzK
  let Z := boundedComplexHomologySequence lam hfg (fun j ↦ z j ^ v)
    (le_radical_span_pow z hJ v) (hfin v hv) K hK.1 (fun n j ↦ hn j n) q
  let eZ : (supportedSequenceHomology lam hfg z hJ hfin q).obj
      ⟨sequenceHomotopyObj K hK.1, hzK⟩ ≅ Z :=
    ObjectProperty.isoMk _ (sequenceHomologyComplexIso K hK.1 q)
  exact (boundedComplexHomologySequence_isZero lam hfg (fun j ↦ z j ^ v)
    (le_radical_span_pow z hJ v) (hfin v hv) U hU hs K hK (fun n j ↦ hn j n) q).of_iso
    ((lengthSerreQuotientFunctor lam s U hU hs).mapIso eZ)

/-- ホモトピー同型で小さいランクの代表をもつ対象も零に送られる。 -/
lemma supportedSequenceQuotientHomology_small
    (P : (supportedSequence (s := s) z).FullSubcategory) (hP : rankSmallBounded P.obj) (q : ℤ) :
    IsZero ((supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).obj P) := by
  obtain ⟨Y, hY, ⟨iY⟩⟩ := hP
  obtain ⟨K, rfl⟩ := Y.quotient_obj_surjective
  have hK := (rankSmallHomotopy_quotient K).mp hY
  let iK : sequenceHomotopyObj K hK.1 ≅ P.obj := ObjectProperty.isoMk _ iY.symm
  have hzK := (supportedSequence z).prop_of_iso iK.symm P.property
  let iP : (⟨sequenceHomotopyObj K hK.1, hzK⟩ : (supportedSequence z).FullSubcategory) ≅ P :=
    ObjectProperty.isoMk _ iK
  exact (supportedSequenceQuotientHomology_smallComplex lam hfg z hJ hfin U hU hs K hK hzK q).of_iso
    ((supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q).mapIso iP.symm)

variable [Nontrivial R]

/-- 長さの商へのホモロジー評価は支持つきランク商の分母を同型に送る。 -/
lemma supportedSequenceQuotientHomology_inverts (q : ℤ) :
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.IsInvertedBy
      (supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q) :=
  homological_inverts_of_kills _ _
    (fun P hP ↦ supportedSequenceQuotientHomology_small lam hfg z hJ hfin U hU hs P hP q)

/-- 支持つき Verdier 商から長さの Serre 商へのホモロジー関手。 -/
noncomputable def supportedRankHomology (q : ℤ) :
    SupportedSequenceRankQuotient (s := s) z ⥤ LengthSerreQuotient lam s U hU hs :=
  Localization.lift (supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q)
    (supportedSequenceQuotientHomology_inverts lam hfg z hJ hfin U hU hs q)
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q

/-- 商上のホモロジー関手は、元の支持つき列上の評価と自然同型で一致する。 -/
noncomputable def supportedRankHomologyFactors (q : ℤ) :
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q ⋙
      supportedRankHomology lam hfg z hJ hfin U hU hs q ≅
        supportedSequenceQuotientHomology lam hfg z hJ hfin U hU hs q :=
  Localization.fac _ (supportedSequenceQuotientHomology_inverts lam hfg z hJ hfin U hU hs q) _

/-- 降下したホモロジー評価も完全三角形を完全列に送る。 -/
instance supportedRankHomology_isHomological (q : ℤ) :
    (supportedRankHomology lam hfg z hJ hfin U hU hs q).IsHomological := by
  let B := rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι
  let := Localization.essSurj_mapArrow B.trW.Q B.trW
  exact Functor.isHomological_of_localization B.trW.Q _ _
    (supportedRankHomologyFactors lam hfg z hJ hfin U hU hs q)

set_option synthInstance.maxSize 512 in
/-- 商上のホモロジー関手は加法的である。 -/
instance supportedRankHomology_additive (q : ℤ) :
    (supportedRankHomology lam hfg z hJ hfin U hU hs q).Additive := inferInstance

end SerrePositivity.Asymptotic

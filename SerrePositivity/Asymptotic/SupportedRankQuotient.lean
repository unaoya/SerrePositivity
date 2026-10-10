module

public import SerrePositivity.Asymptotic.SequenceLinear
public import SerrePositivity.CategoryTheory.ScalarSupportLocalization

/-!
# 支持部分圏のランク商から全体の商への完全忠実性

共通有界ホモトピー圏で一様に台をもつ対象を先に取り、その中でランク商を取る。
得られる関手の完全忠実性は、スカラーの錐を反復する一般の因子化定理から従う。
商に移した後で初めて台をもつ対象も定義するが、本質像や冪等完備化との比較は別の課題。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}
  {e : ℕ} (z : Fin e → R)

/-- 商を取る前に共通の冪で台をもつ有界自由列。 -/
abbrev supportedSequence : ObjectProperty (SequenceHomotopy R s) := scalarSupported z

/-- ランク商の中で共通の冪で台をもつ対象。 -/
abbrev supportedRankQuotient : ObjectProperty (SequenceRankQuotient R s) := scalarSupported z

/-- 商の前の支持つき対象は、商に移した後も台をもつ。 -/
lemma supportedSequence_map_quotient (X : SequenceHomotopy R s)
    (hX : supportedSequence z X) :
    supportedRankQuotient z (sequenceRankQuotientFunctor.obj X) :=
  scalarSupported_map z sequenceRankQuotientFunctor X hX

/-- 支持部分圏の中でランクの小さい対象を消す Verdier 商。 -/
abbrev SupportedSequenceRankQuotient :=
  ((rankSmallBounded (R := R) (s := s)).inverseImage (supportedSequence z).ι).trW.Localization

/-- 支持部分圏のランク商から全体のランク商への標準関手。 -/
@[implicit_reducible]
noncomputable def supportedRankQuotientInclusion :
    SupportedSequenceRankQuotient (s := s) z ⥤ SequenceRankQuotient R s :=
  ((supportedSequence z).triangulatedLocalizerMorphism rankSmallBounded).localizedFunctor
    ((rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q)
    sequenceRankQuotientFunctor

noncomputable instance : (supportedRankQuotientInclusion (s := s) z).CommShift ℤ := by
  dsimp only [supportedRankQuotientInclusion]
  infer_instance

/-- 支持部分圏の商からの関手は完全三角形を保存する。 -/
instance : (supportedRankQuotientInclusion (s := s) z).IsTriangulated := by
  let A := supportedSequence (s := s) z
  let B := rankSmallBounded (R := R) (s := s)
  let Φ := A.triangulatedLocalizerMorphism B
  let L := (B.inverseImage A.ι).trW.Q
  let := Localization.essSurj_mapArrow L (B.inverseImage A.ι).trW
  exact Functor.isTriangulated_of_precomp_iso
    (CatCommSq.iso Φ.functor L B.trW.Q (Φ.localizedFunctor L B.trW.Q)).symm

/-- 支持つき小対象を経由する因子化により、商の関手は充満である。 -/
instance : (supportedRankQuotientInclusion (s := s) z).Full := by
  dsimp only [supportedRankQuotientInclusion]
  infer_instance

/-- 同じ因子化により、商の関手は忠実である。 -/
instance : (supportedRankQuotientInclusion (s := s) z).Faithful := by
  dsimp only [supportedRankQuotientInclusion]
  infer_instance

/-- 商で台をもつ対象は、商の前で一様に台をもつ対象の像の直和因子である。 -/
theorem supportedRankQuotient_retract (Y : SequenceRankQuotient R s)
    (hY : supportedRankQuotient z Y) :
    ∃ X : SequenceHomotopy R s, supportedSequence z X ∧
      Nonempty (Retract Y (sequenceRankQuotientFunctor.obj X)) := by
  let := Localization.essSurj (sequenceRankQuotientFunctor (R := R) (s := s))
    (rankSmallBounded (R := R) (s := s)).trW
  exact scalarSupported_retract_image sequenceRankQuotientFunctor z Y hY

end SerrePositivity.Asymptotic

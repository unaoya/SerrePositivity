module

public import SerrePositivity.Asymptotic.CompletedComplexEvaluation
public import SerrePositivity.CategoryTheory.VerdierKaroubiLinear
public import SerrePositivity.CategoryTheory.ScalarSupportEquivalence
public import Mathlib.CategoryTheory.Shift.Linear

/-! # 論文と同じ順序で構成したランク商との比較

論文の D_S = Kar(K^b)、N_S = 小さいランクの列の像が生成する厚い部分圏、
P_S = Kar(D_S/N_S) を構成し、これまで用いた Kar(K^b/N) と線形三角同値で結ぶ。
-/

@[expose] public section

universe u

set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents
open CategoryTheory.Limits

variable (R : Type u) [CommRing R] [Nontrivial R] (s : ℕ → ℕ)

/-- 論文の D_S：共通有界な自由列のホモトピー圏の冪等完備化。 -/
abbrev PaperSequenceCategory := Karoubi (SequenceHomotopy R s)

/-- 論文の N_S：小さいランクの列の像から生成される厚い部分圏。 -/
abbrev paperRankNull : ObjectProperty (PaperSequenceCategory R s) :=
  karoubiNullEnvelope (rankSmallBounded (R := R) (s := s))

/-- 論文の P_S：完備化、厚い部分圏による商、再び完備化の順で構成する。 -/
abbrev PaperRankQuotient := Karoubi ((paperRankNull R s).trW.Localization)

noncomputable abbrev paperRankEquivalence :
    PaperRankQuotient R s ≌ CompletedSequenceRankQuotient R s :=
  karoubiVerdierOrderEquivalence (rankSmallBounded (R := R) (s := s))

noncomputable abbrev paperSequenceFunctor : SequenceHomotopy R s ⥤ PaperRankQuotient R s :=
  karoubiFirstFromOriginal (rankSmallBounded (R := R) (s := s))

/-- 実際の複体列からの標準関手との両立。 -/
noncomputable def paperSequenceComparison :
    paperSequenceFunctor R s ⋙ (paperRankEquivalence R s).functor ≅ completedSequenceFunctor :=
  isoWhiskerLeft (toKaroubi _ ⋙ (paperRankNull R s).trW.Q)
    (completedKaroubiFirstToLastFactors _) ≪≫
  isoWhiskerLeft (toKaroubi _) (karoubiFirstToLastFactors _) ≪≫
    (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app sequenceRankQuotientFunctor

variable {R s} {e : ℕ} (z : Fin e → R)

/-- 論文の P_S^J に対応する支持部分圏。 -/
abbrev paperSupportedRank : ObjectProperty (PaperRankQuotient R s) := scalarSupported z

/-- 論文の支持部分圏と構成済みの評価の定義域との線形三角同値。 -/
noncomputable abbrev paperSupportedRankEquivalence :
    (paperSupportedRank (s := s) z).FullSubcategory ≌
      (supportedCompletedRankQuotient (s := s) z).FullSubcategory :=
  scalarSupportEquivalence (paperRankEquivalence R s) z

/-- 支持つき商の完備化との比較も合成で得られる。 -/
noncomputable def paperSupportedToKaroubi :
    (paperSupportedRank (s := s) z).FullSubcategory ≌
      Karoubi (SupportedSequenceRankQuotient (s := s) z) :=
  (paperSupportedRankEquivalence z).trans (supportedKaroubiEquivalence z).symm

noncomputable instance paperSupportedToKaroubi_functor_commShift :
    (paperSupportedToKaroubi (s := s) z).functor.CommShift ℤ :=
  inferInstanceAs (((paperSupportedRankEquivalence z).functor ⋙
    (supportedKaroubiEquivalence z).inverse).CommShift ℤ)

noncomputable instance paperSupportedToKaroubi_inverse_commShift :
    (paperSupportedToKaroubi (s := s) z).inverse.CommShift ℤ :=
  inferInstanceAs (((supportedKaroubiEquivalence z).functor ⋙
    (paperSupportedRankEquivalence z).inverse).CommShift ℤ)

instance paperSupportedToKaroubi_functor_isTriangulated :
    (paperSupportedToKaroubi (s := s) z).functor.IsTriangulated :=
  inferInstanceAs (((paperSupportedRankEquivalence z).functor ⋙
    (supportedKaroubiEquivalence z).inverse).IsTriangulated)

instance paperSupportedToKaroubi_inverse_isTriangulated :
    (paperSupportedToKaroubi (s := s) z).inverse.IsTriangulated :=
  inferInstanceAs (((supportedKaroubiEquivalence z).functor ⋙
    (paperSupportedRankEquivalence z).inverse).IsTriangulated)

end SerrePositivity.Asymptotic

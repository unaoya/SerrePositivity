module

public import SerrePositivity.Asymptotic.SequenceBaseChangeSupport
public import SerrePositivity.Asymptotic.SupportedKaroubi

/-!
# 支持つきランク商の係数変更

一様な台の保存により係数変更を支持部分圏に制限し、小さいランクの Verdier 商に降ろす。
商をとる前後の関手の自然同型と、シフト・完全三角形との両立を備える。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory

variable {R S : Type u} [CommRing R] [CommRing S] {s : ℕ → ℕ}
  (φ : R →+* S) {e : ℕ} (z : Fin e → R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 共通有界ホモトピー圏の支持条件は係数変更で保たれる。 -/
lemma changeRing_supportedSequence (X : SequenceHomotopy R s) (hX : supportedSequence z X) :
    supportedSequence (φ ∘ z) ((mapBoundedHomotopy (FreeSequence.changeRing φ)).obj X) := by
  obtain ⟨Y, hY⟩ := X
  obtain ⟨K, rfl⟩ := Y.quotient_obj_surjective
  exact changeRing_complex_supported φ z K ((boundedHomotopyProperty_quotient _ K).mp hY) hX

/-- 一様に台をもつ自由列のホモトピー圏の係数変更関手。 -/
@[implicit_reducible]
noncomputable def supportedSequenceChangeRing :
    (supportedSequence (s := s) z).FullSubcategory ⥤
      (supportedSequence (s := s) (φ ∘ z)).FullSubcategory :=
  (supportedSequence (φ ∘ z)).lift
    ((supportedSequence z).ι ⋙ mapBoundedHomotopy (FreeSequence.changeRing φ))
    (fun X ↦ changeRing_supportedSequence φ z X.obj X.property)

noncomputable instance supportedSequenceChangeRing_commShift :
    (supportedSequenceChangeRing (s := s) φ z).CommShift ℤ := by
  dsimp only [supportedSequenceChangeRing]
  infer_instance

instance supportedSequenceChangeRing_isTriangulated :
    (supportedSequenceChangeRing (s := s) φ z).IsTriangulated := by
  dsimp only [supportedSequenceChangeRing]
  infer_instance

variable [Nontrivial R] [Nontrivial S]

omit [Nontrivial R] [Nontrivial S] in
/-- 支持つき商への係数変更は、支持つき小対象を錐とする分母を可逆にする。 -/
lemma supportedSequenceChangeRing_inverts :
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.IsInvertedBy
      (supportedSequenceChangeRing φ z ⋙
        (rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q) := by
  let F := supportedSequenceChangeRing (s := s) φ z
  let P := rankSmallBounded.inverseImage (supportedSequence (s := s) (φ ∘ z)).ι
  have h : rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι ≤ P.inverseImage F :=
    fun X hX ↦ changeRing_rankSmallBounded φ X.obj hX
  intro X Y f hf
  exact P.inverseImage_trW_isInverted F P.trW.Q f
    (ObjectProperty.trW_monotone h f hf)

/-- 支持部分圏のランク商に誘導される係数変更関手。 -/
@[implicit_reducible]
noncomputable def supportedRankChangeRing :
    SupportedSequenceRankQuotient (s := s) z ⥤
      SupportedSequenceRankQuotient (s := s) (φ ∘ z) :=
  Localization.lift
    (supportedSequenceChangeRing φ z ⋙
      (rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q)
    (supportedSequenceChangeRing_inverts φ z)
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q

/-- 商の前後での支持つき係数変更を比較する自然同型。 -/
noncomputable def supportedRankChangeRingFactors :
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q ⋙
      supportedRankChangeRing φ z ≅
    supportedSequenceChangeRing φ z ⋙
      (rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q :=
  Localization.fac _ (supportedSequenceChangeRing_inverts φ z) _

noncomputable instance supportedRankChangeRing_lifting : Localization.Lifting
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW
    (supportedSequenceChangeRing φ z ⋙
      (rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q)
    (supportedRankChangeRing φ z) := ⟨supportedRankChangeRingFactors φ z⟩

noncomputable instance supportedRankChangeRing_commShift :
    (supportedRankChangeRing (s := s) φ z).CommShift ℤ :=
  Functor.commShiftOfLocalization
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW ℤ
    (supportedSequenceChangeRing φ z ⋙
      (rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q)
    (supportedRankChangeRing φ z)

instance supportedRankChangeRingFactors_commShift :
    NatTrans.CommShift (supportedRankChangeRingFactors (s := s) φ z).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW.Q
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW ℤ
    (supportedSequenceChangeRing φ z ⋙
      (rankSmallBounded.inverseImage (supportedSequence (φ ∘ z)).ι).trW.Q)
    (supportedRankChangeRing φ z)

/-- 支持つきランク商の係数変更は三角関手である。 -/
instance supportedRankChangeRing_isTriangulated :
    (supportedRankChangeRing (s := s) φ z).IsTriangulated := by
  let := Localization.essSurj_mapArrow
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
    (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW
  exact Functor.isTriangulated_of_precomp_iso (supportedRankChangeRingFactors φ z)

end SerrePositivity.Asymptotic

module

public import SerrePositivity.Asymptotic.CompletedBaseChangeSupport
public import SerrePositivity.Asymptotic.PaperBaseChange

/-! # 支持部分圏と全体の圏での係数変更の比較 -/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents

variable {R S : Type u} [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
  {s : ℕ → ℕ} (φ : R →+* S) {e : ℕ} (z : Fin e → R)

/-- 支持を忘れる関手と商の係数変更の可換性。 -/
noncomputable def supportedRankChangeRingInclusionIso :
    supportedRankChangeRing (s := s) φ z ⋙ supportedRankQuotientInclusion (φ ∘ z) ≅
      supportedRankQuotientInclusion z ⋙ rankQuotientChangeRing φ := by
  let A := supportedSequence (s := s) z
  let A' := supportedSequence (s := s) (φ ∘ z)
  let B := rankSmallBounded (R := R) (s := s)
  let B' := rankSmallBounded (R := S) (s := s)
  let Q := (B.inverseImage A.ι).trW.Q
  let Q' := (B'.inverseImage A'.ι).trW.Q
  let Φ := A.triangulatedLocalizerMorphism B
  let Ψ := A'.triangulatedLocalizerMorphism B'
  let i := CatCommSq.iso Φ.functor Q B.trW.Q (Φ.localizedFunctor Q B.trW.Q)
  let j := CatCommSq.iso Ψ.functor Q' B'.trW.Q (Ψ.localizedFunctor Q' B'.trW.Q)
  exact (Localization.fullyFaithfulWhiskeringLeft Q (B.inverseImage A.ι).trW _).preimageIso
    (isoWhiskerRight (supportedRankChangeRingFactors φ z) (supportedRankQuotientInclusion _) ≪≫
      isoWhiskerLeft (supportedSequenceChangeRing φ z) j.symm ≪≫
      isoWhiskerLeft A.ι (rankQuotientChangeRing_fac φ).symm ≪≫
      isoWhiskerRight i (rankQuotientChangeRing φ))

/-- 全体の完備化上の係数変更を支持部分圏に制限する。 -/
@[implicit_reducible] noncomputable def completedSupportedChangeRing :
    (supportedCompletedRankQuotient (s := s) z).FullSubcategory ⥤
      (supportedCompletedRankQuotient (s := s) (φ ∘ z)).FullSubcategory :=
  (supportedCompletedRankQuotient (φ ∘ z)).lift
    ((supportedCompletedRankQuotient z).ι ⋙ completedChangeRing φ)
    (fun X ↦ completedChangeRing_supported φ z X.obj X.property)

noncomputable instance : (completedSupportedChangeRing (s := s) φ z).CommShift ℤ := by
  dsimp only [completedSupportedChangeRing]
  infer_instance

instance : (completedSupportedChangeRing (s := s) φ z).IsTriangulated := by
  dsimp only [completedSupportedChangeRing]
  infer_instance

/-- 支持つき商の完備化と全体の商の完備化での係数変更が一致する。 -/
noncomputable def supportedKaroubiChangeRingIso :
    (functorExtension₂ _ _).obj (supportedRankChangeRing (s := s) φ z) ⋙
      (supportedKaroubiEquivalence (φ ∘ z)).functor ≅
    (supportedKaroubiEquivalence z).functor ⋙ completedSupportedChangeRing φ z := by
  let F := supportedRankChangeRing (s := s) φ z
  let I := supportedRankQuotientInclusion (s := s) z
  let J := supportedRankQuotientInclusion (s := s) (φ ∘ z)
  let G := rankQuotientChangeRing (s := s) φ
  let F' := (functorExtension₂ _ _).obj F
  let I' := (functorExtension₂ _ _).obj I
  let J' := (functorExtension₂ _ _).obj J
  let G' := (functorExtension₂ _ _).obj G
  let a : toKaroubi _ ⋙ F' ⋙ J' ≅ toKaroubi _ ⋙ I' ⋙ G' :=
    isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app F) J' ≪≫
    isoWhiskerLeft F ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app J) ≪≫
    isoWhiskerRight (supportedRankChangeRingInclusionIso φ z) (toKaroubi _) ≪≫
    isoWhiskerLeft I ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app G).symm ≪≫
    isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app I).symm G'
  let b : F' ⋙ J' ≅ I' ⋙ G' :=
    ((whiskeringLeft _ _ _).obj (toKaroubi _)).preimageIso a
  exact ((supportedCompletedRankQuotient (s := s) (φ ∘ z)).fullyFaithfulι.whiskeringRight
    (Karoubi (SupportedSequenceRankQuotient (s := s) z))).preimageIso b

/-- 論文の圏の係数変更も、全体の圏の係数変更を制限したものと一致する。 -/
noncomputable def paperChangeRingToCompletedIso :
    paperSupportedChangeRing (s := s) φ z ⋙ (paperSupportedRankEquivalence (φ ∘ z)).functor ≅
      (paperSupportedRankEquivalence z).functor ⋙ completedSupportedChangeRing φ z :=
  isoWhiskerLeft (paperSupportedChangeRing φ z ⋙
    (paperSupportedRankEquivalence (φ ∘ z)).functor)
    (supportedKaroubiEquivalence (φ ∘ z)).counitIso.symm ≪≫
  isoWhiskerRight (paperSupportedChangeRingFactors φ z)
    (supportedKaroubiEquivalence (φ ∘ z)).functor ≪≫
  isoWhiskerLeft (paperSupportedToKaroubi z).functor (supportedKaroubiChangeRingIso φ z) ≪≫
  isoWhiskerRight (isoWhiskerLeft (paperSupportedRankEquivalence z).functor
    (supportedKaroubiEquivalence z).counitIso) (completedSupportedChangeRing φ z)

end SerrePositivity.Asymptotic

module

public import SerrePositivity.Asymptotic.SupportedRankBaseChange
public import SerrePositivity.CategoryTheory.Karoubi.Triangulated

/-! # 二段階の係数変更と直接の係数変更との比較 -/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {s : ℕ → ℕ}
  (φ : R →+* S) (ψ : S →+* T)

lemma FreeSequence.changeMatrix_changeMatrix {a b : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    changeMatrix ψ (changeMatrix φ f) = changeMatrix (ψ.comp φ) f := by
  simp only [changeMatrix, LinearMap.toMatrix'_toLin']
  rfl

noncomputable def FreeSequence.changeRingCompIso :
    changeRing (s := s) φ ⋙ changeRing ψ ≅ changeRing (ψ.comp φ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp only [Category.comp_id, Category.id_comp, Iso.refl_hom]
    funext n
    exact changeMatrix_changeMatrix φ ψ (f n))

noncomputable def sequenceChangeRingCompIso :
    mapBoundedHomotopy (FreeSequence.changeRing (s := s) φ) ⋙
      mapBoundedHomotopy (FreeSequence.changeRing ψ) ≅
        mapBoundedHomotopy (FreeSequence.changeRing (ψ.comp φ)) :=
  ((boundedHomotopyProperty (FreeSequence T s)).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (boundedHomotopyInclusion _) (Functor.mapHomotopyCategoryCompIso
      (FreeSequence.changeRingCompIso (s := s) φ ψ) (.up ℤ)))

variable {e : ℕ} (z : Fin e → R)

noncomputable def supportedSequenceChangeRingCompIso :
    supportedSequenceChangeRing (s := s) φ z ⋙ supportedSequenceChangeRing ψ (φ ∘ z) ≅
      supportedSequenceChangeRing (ψ.comp φ) z :=
  ((supportedSequence (s := s) ((ψ.comp φ) ∘ z)).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (supportedSequence z).ι (sequenceChangeRingCompIso φ ψ))

variable [Nontrivial R] [Nontrivial S] [Nontrivial T]

/-- 二段階の支持つき Verdier 商の係数変更は直接の係数変更に自然同型。 -/
noncomputable def supportedRankChangeRingCompIso :
    supportedRankChangeRing (s := s) φ z ⋙ supportedRankChangeRing ψ (φ ∘ z) ≅
      supportedRankChangeRing (ψ.comp φ) z := by
  let Q := (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
  let Q' := (rankSmallBounded.inverseImage
    (supportedSequence (s := s) ((ψ.comp φ) ∘ z)).ι).trW.Q
  let i : Q ⋙ supportedRankChangeRing φ z ⋙ supportedRankChangeRing ψ (φ ∘ z) ≅
      Q ⋙ supportedRankChangeRing (ψ.comp φ) z :=
    isoWhiskerRight (supportedRankChangeRingFactors φ z) (supportedRankChangeRing ψ (φ ∘ z)) ≪≫
    isoWhiskerLeft (supportedSequenceChangeRing φ z) (supportedRankChangeRingFactors ψ (φ ∘ z)) ≪≫
    isoWhiskerRight (supportedSequenceChangeRingCompIso φ ψ z) Q' ≪≫
    (supportedRankChangeRingFactors (ψ.comp φ) z).symm
  exact (Localization.fullyFaithfulWhiskeringLeft Q
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW _).preimageIso i

/-- 冪等完備化後も二段階と直接の係数変更は一致する。 -/
noncomputable def completedSupportedChangeRingCompIso :
    (functorExtension₂ _ _).obj (supportedRankChangeRing (s := s) φ z) ⋙
      (functorExtension₂ _ _).obj (supportedRankChangeRing ψ (φ ∘ z)) ≅
        (functorExtension₂ _ _).obj (supportedRankChangeRing (ψ.comp φ) z) := by
  let F := supportedRankChangeRing (s := s) φ z
  let G := supportedRankChangeRing (s := s) ψ (φ ∘ z)
  let H := supportedRankChangeRing (s := s) (ψ.comp φ) z
  let F' := (functorExtension₂ _ _).obj F
  let G' := (functorExtension₂ _ _).obj G
  let H' := (functorExtension₂ _ _).obj H
  let i : toKaroubi _ ⋙ F' ⋙ G' ≅ toKaroubi _ ⋙ H' :=
    isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app F) G' ≪≫
    isoWhiskerLeft F ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app G) ≪≫
    isoWhiskerRight (supportedRankChangeRingCompIso φ ψ z) (toKaroubi _) ≪≫
    ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app H).symm
  exact ((whiskeringLeft _ _ _).obj (toKaroubi _)).preimageIso i

end SerrePositivity.Asymptotic

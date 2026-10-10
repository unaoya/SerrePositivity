module

public import SerrePositivity.Asymptotic.PaperBaseChange

/-! # 恒等係数変更

自由列から支持つき商・冪等完備化まで恒等係数変更を比較する。
自己同型によるひねりの単位元の法則に用いる。
-/

@[expose] public section

universe u

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Functor CategoryTheory.Idempotents

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 恒等環準同型による自由列の係数変更。 -/
noncomputable def FreeSequence.changeRingIdIso :
    changeRing (s := s) (RingHom.id R) ≅ 𝟭 (FreeSequence R s) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    funext n
    simp [changeRing, changeMatrix])

/-- 恒等加法関手がホモトピー圏に誘導する関手。 -/
noncomputable def freeSequenceHomotopyIdIso :
    (𝟭 (FreeSequence R s)).mapHomotopyCategory (.up ℤ) ≅
      𝟭 (HomotopyCategory (FreeSequence R s) (.up ℤ)) :=
  Quotient.natIsoLift _ (isoWhiskerRight
    (Functor.mapHomologicalComplexIdIso (FreeSequence R s) (.up ℤ))
    (HomotopyCategory.quotient _ _))

/-- 共通有界ホモトピー圏の恒等係数変更。 -/
noncomputable def sequenceChangeRingIdIso :
    mapBoundedHomotopy (FreeSequence.changeRing (s := s) (RingHom.id R)) ≅
      𝟭 (SequenceHomotopy R s) :=
  ((boundedHomotopyProperty (FreeSequence R s)).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (boundedHomotopyInclusion _)
      ((NatIso.mapHomotopyCategory FreeSequence.changeRingIdIso (.up ℤ)) ≪≫
        freeSequenceHomotopyIdIso))

variable {e : ℕ} (z : Fin e → R)

/-- 支持部分圏の恒等係数変更。 -/
noncomputable def supportedSequenceChangeRingIdIso :
    supportedSequenceChangeRing (s := s) (RingHom.id R) z ≅
      𝟭 (supportedSequence (s := s) z).FullSubcategory :=
  ((supportedSequence (s := s) z).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (supportedSequence z).ι sequenceChangeRingIdIso)

variable [Nontrivial R]

/-- 支持つき Verdier 商の恒等係数変更。 -/
noncomputable def supportedRankChangeRingIdIso :
    supportedRankChangeRing (s := s) (RingHom.id R) z ≅
      𝟭 (SupportedSequenceRankQuotient (s := s) z) := by
  let Q := (rankSmallBounded.inverseImage (supportedSequence (s := s) z).ι).trW.Q
  exact (Localization.fullyFaithfulWhiskeringLeft Q
    (rankSmallBounded.inverseImage (supportedSequence z).ι).trW _).preimageIso
      (supportedRankChangeRingFactors (RingHom.id R) z ≪≫
        isoWhiskerRight (supportedSequenceChangeRingIdIso z) Q)

/-- 冪等完備化した支持つき商の恒等係数変更。 -/
noncomputable def completedSupportedChangeRingIdIso :
    (functorExtension₂ _ _).obj (supportedRankChangeRing (s := s) (RingHom.id R) z) ≅
      𝟭 (Karoubi (SupportedSequenceRankQuotient (s := s) z)) := by
  exact ((whiskeringLeft _ _ _).obj (toKaroubi _)).preimageIso
    ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app _ ≪≫
      isoWhiskerRight (supportedRankChangeRingIdIso z) (toKaroubi _))

/-- 論文の支持圏の恒等係数変更。 -/
noncomputable def paperSupportedChangeRingIdIso :
    paperSupportedChangeRing (s := s) (RingHom.id R) z ≅
      𝟭 (paperSupportedRank (s := s) z).FullSubcategory :=
  isoWhiskerLeft (paperSupportedToKaroubi z).functor
    (isoWhiskerRight (completedSupportedChangeRingIdIso z)
      (paperSupportedToKaroubi z).inverse) ≪≫
    (paperSupportedToKaroubi z).unitIso.symm

/-- 恒等係数変更が K₀ に誘導する写像は恒等写像。 -/
lemma paperSupportedChangeRingK0_id :
    TriangulatedK0.map (paperSupportedChangeRing (s := s) (RingHom.id R) z) =
      AddMonoidHom.id _ := by
  apply TriangulatedK0.hom_ext
  intro X
  exact TriangulatedK0.mk_iso ((paperSupportedChangeRingIdIso z).app X)

end SerrePositivity.Asymptotic

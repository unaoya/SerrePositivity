module

public import SerrePositivity.Asymptotic.SupportedRankQuotient
public import SerrePositivity.CategoryTheory.ScalarSupport

/-!
# 支持つきランク商の冪等完備化

支持部分圏のランク商を冪等完備化した圏と、全体のランク商を冪等完備化してから
台を課した圏を比較する。前段で得た完全忠実性と、形式的直和因子の支持つき表示を使う。
ここでの同値は圏としての同値であり、Karoubi 包絡の三角構造との両立は別に扱う。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Idempotents

variable {R : Type u} [CommRing R] [Nontrivial R] {s : ℕ → ℕ}
  {e : ℕ} (z : Fin e → R)

/-- ランク商の加法的冪等完備化。論文の圏との三角的な比較は別途必要である。 -/
abbrev CompletedSequenceRankQuotient (R : Type u) [CommRing R] [Nontrivial R] (s : ℕ → ℕ) :=
  Karoubi (SequenceRankQuotient R s)

/-- 冪等完備化したランク商で台をもつ対象の条件。 -/
abbrev supportedCompletedRankQuotient : ObjectProperty (CompletedSequenceRankQuotient R s) :=
  scalarSupported z

/-- 支持部分圏の商の対象は、全体の商への像で台をもつ。 -/
lemma supportedRankQuotientInclusion_supported (Y : SupportedSequenceRankQuotient (s := s) z) :
    supportedRankQuotient z ((supportedRankQuotientInclusion z).obj Y) := by
  let A := supportedSequence (s := s) z
  let B := rankSmallBounded (R := R) (s := s)
  let L := (B.inverseImage A.ι).trW.Q
  let Φ := A.triangulatedLocalizerMorphism B
  let F := supportedRankQuotientInclusion (s := s) z
  let := Localization.essSurj L (B.inverseImage A.ι).trW
  let X := L.objPreimage Y
  have hX := supportedSequence_map_quotient z X.obj X.property
  let i : sequenceRankQuotientFunctor.obj X.obj ≅ F.obj Y :=
    (CatCommSq.iso Φ.functor L B.trW.Q (Φ.localizedFunctor L B.trW.Q)).app X ≪≫
      F.mapIso (L.objObjPreimageIso Y)
  exact (supportedRankQuotient z).prop_of_iso i hX

/-- 延長した包含関手の像は、冪等完備化後も台をもつ。 -/
lemma supportedKaroubi_image (P : Karoubi (SupportedSequenceRankQuotient (s := s) z)) :
    supportedCompletedRankQuotient z
      (((functorExtension₂ _ _).obj (supportedRankQuotientInclusion z)).obj P) := by
  let F := supportedRankQuotientInclusion (s := s) z
  have h := scalarSupported_map z (toKaroubi _) (F.obj P.X)
    (supportedRankQuotientInclusion_supported z P.X)
  let i := ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app F).app P.X
  exact (scalarSupported z).prop_of_retract
    ((karoubiRetract P).map ((functorExtension₂ _ _).obj F))
    ((scalarSupported z).prop_of_iso i.symm h)

/-- 冪等完備化後に台をもつ対象は、支持部分圏の商の延長された像に属する。 -/
theorem supportedKaroubi_mem_essImage (P : CompletedSequenceRankQuotient R s)
    (hP : supportedCompletedRankQuotient z P) :
    ((functorExtension₂ _ _).obj (supportedRankQuotientInclusion (s := s) z)).essImage P := by
  let A := supportedSequence (s := s) z
  let B := rankSmallBounded (R := R) (s := s)
  let L := (B.inverseImage A.ι).trW.Q
  let Φ := A.triangulatedLocalizerMorphism B
  let F := supportedRankQuotientInclusion (s := s) z
  let := Localization.essSurj (sequenceRankQuotientFunctor (R := R) (s := s)) B.trW
  obtain ⟨X, hX, ⟨r⟩⟩ :=
    karoubi_scalarSupported_retract_image sequenceRankQuotientFunctor z P hP
  let X' : A.FullSubcategory := ⟨X, hX⟩
  let i : sequenceRankQuotientFunctor.obj X ≅ F.obj (L.obj X') :=
    (CatCommSq.iso Φ.functor L B.trW.Q (Φ.localizedFunctor L B.trW.Q)).app X'
  exact karoubiExtension_mem_essImage F P (L.obj X')
    (r.trans (Retract.ofIso ((toKaroubi _).mapIso i)))

/-- 冪等完備化した包含関手の本質像は、商の冪等完備化で台をもつ対象全体である。 -/
theorem supportedKaroubi_essImage :
    ((functorExtension₂ _ _).obj (supportedRankQuotientInclusion (s := s) z)).essImage =
      supportedCompletedRankQuotient z := by
  ext P
  constructor
  · rintro ⟨Q, ⟨i⟩⟩
    exact (supportedCompletedRankQuotient z).prop_of_iso i (supportedKaroubi_image z Q)
  · exact supportedKaroubi_mem_essImage z P

/-- 延長した包含を支持部分圏に制限した関手。 -/
noncomputable def supportedKaroubiFunctor :
    Karoubi (SupportedSequenceRankQuotient (s := s) z) ⥤
      (supportedCompletedRankQuotient (s := s) z).FullSubcategory :=
  (supportedCompletedRankQuotient z).lift
    ((functorExtension₂ _ _).obj (supportedRankQuotientInclusion z))
    (supportedKaroubi_image z)

instance supportedKaroubiFunctor_full : (supportedKaroubiFunctor (s := s) z).Full := by
  dsimp only [supportedKaroubiFunctor]
  infer_instance

instance supportedKaroubiFunctor_faithful : (supportedKaroubiFunctor (s := s) z).Faithful := by
  dsimp only [supportedKaroubiFunctor]
  infer_instance

instance supportedKaroubiFunctor_essSurj : (supportedKaroubiFunctor (s := s) z).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, ⟨e⟩⟩ := supportedKaroubi_mem_essImage z Y.obj Y.property
    exact ⟨X, ⟨ObjectProperty.isoMk _ e⟩⟩

instance supportedKaroubiFunctor_isEquivalence :
    (supportedKaroubiFunctor (s := s) z).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- 冪等完備化した支持部分圏の商と、冪等完備化後の支持部分圏との圏同値。 -/
noncomputable def supportedKaroubiEquivalence :
    Karoubi (SupportedSequenceRankQuotient (s := s) z) ≌
      (supportedCompletedRankQuotient (s := s) z).FullSubcategory :=
  (supportedKaroubiFunctor z).asEquivalence

end SerrePositivity.Asymptotic

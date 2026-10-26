module

public import SerrePositivity.KST.NonConnective.SequentialLevelColimit

/-!
概要：段ごとの逐次 BF 余錐の、厳密な BF 射の圏での普遍性。
方針：各段の余極限射を suspension の余極限保存で構造射と照合する。
規約：通常の圏の IsColimit。∞ 圏の IsColimitCone と区別する。
使われ方：K-7 の全反変 Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 任意の厳密な BF 余錐へ、各段で余極限の普遍射を取った実 BF 射。 -/
def sequentialLevelColimitDesc (D : SpectrumSequence.{u}) (s : Cocone D) :
    sequentialLevelColimitSpectrum D ⟶ s.pt :=
  FilteredExchange.levelColimitDesc D s


/-- 段ごとの余錐は厳密な BF 射の通常の圏で余極限。 -/
def sequentialLevelColimitIsColimit (D : SpectrumSequence.{u}) :
    IsColimit (sequentialLevelColimitCocone D) where
  desc := sequentialLevelColimitDesc D
  fac s a := by
    apply OmegaSpectrum.Hom.ext
    intro k
    exact colimit.ι_desc ((OmegaSpectrum.levelEvaluation k).mapCocone s) a
  uniq s m hm := by
    apply OmegaSpectrum.Hom.ext
    intro k
    apply colimit.hom_ext
    intro a
    have h := congrArg (fun f ↦ f.app k) (hm a)
    exact h.trans (colimit.ι_desc ((OmegaSpectrum.levelEvaluation k).mapCocone s) a).symm

end SerrePositivity.KST.NonConnective

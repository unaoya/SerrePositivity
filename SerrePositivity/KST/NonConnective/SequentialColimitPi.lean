module

public import SerrePositivity.KST.NonConnective.SequentialColimit

/-!
概要：元の実 Sp 余極限余錐の各脚と、全整数 π の余極限比較。
方針：元の BF 射影と各注入の厳密な合成式で、既存の群余極限から移す。
規約：対象の群同型だけでなく、同じ元の注入射を持つ群 cocone の普遍性。
使われ方：K-7 工程 1 の π_* との交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 元の各段から候補への射と元の BF 射影の合成は、実余極限余錐の厳密な脚。 -/
lemma sequentialInjection_projection (D : SpectrumSequence.{u}) (a : SequentialIndex.{u}) :
    OmegaSpectrum.filteredSpectrumInjection D a ≫ sequentialReplacementProjection D =
      sequentialLevelColimitInjection D a := by
  apply OmegaSpectrum.Hom.ext
  intro k
  exact OmegaSpectrum.filteredSpectrumInjection_comparison D a k

/-- 元の段ごとの実余極限余錐を、整数次数の群へ写した同じ群余錐。 -/
def sequentialLevelPiCocone (D : SpectrumSequence.{u}) (j : ℤ) :
    Cocone (OmegaSpectrum.spectrumHomotopyGroupDiagram D j) :=
  (OmegaSpectrum.homotopyFunctor j ⋙ forget₂ CommGrpCat GrpCat).mapCocone
    (sequentialLevelColimitCocone D)

/-- 既存の候補の群余錐と、実 Sp 余極限の元の脚の群余錐との同型。 -/
def sequentialLevelPiCoconeIso (D : SpectrumSequence.{u}) (j : ℤ) :
    sequentialPiCocone D j ≅ sequentialLevelPiCocone D j :=
  Cocone.ext ((sequentialReplacementProjection_piIsomorphism D).groupEquiv j).toGrpIso (by
    intro a
    apply ConcreteCategory.hom_ext
    intro x
    change OmegaSpectrum.homotopyMap (sequentialReplacementProjection D) j
      (OmegaSpectrum.homotopyMap (OmegaSpectrum.filteredSpectrumInjection D a) j x) =
        OmegaSpectrum.homotopyMap (sequentialLevelColimitInjection D a) j x
    rw [← MonoidHom.comp_apply, ← OmegaSpectrum.homotopyMap_comp, sequentialInjection_projection])

/-- 元の実 Sp 余極限余錐の同じ各脚は、全整数次数で群の余極限を与える。 -/
def sequentialLevelPiCoconeIsColimit (D : SpectrumSequence.{u}) (j : ℤ) :
    IsColimit (sequentialLevelPiCocone D j) :=
  IsColimit.ofIsoColimit (sequentialPiCoconeIsColimit D j) (sequentialLevelPiCoconeIso D j)

/-- 全整数次数における、元の図式の群余極限から実 Sp 余極限の群への比較同型。 -/
def sequentialLevelColimitHomotopyIso (D : SpectrumSequence.{u}) (j : ℤ) :
    colimit (OmegaSpectrum.spectrumHomotopyGroupDiagram D j) ≅
      GrpCat.of (OmegaSpectrum.homotopyGroup (sequentialLevelColimitSpectrum D) j) :=
  OmegaSpectrum.filteredSpectrumHomotopyIso D j ≪≫
    ((sequentialReplacementProjection_piIsomorphism D).groupEquiv j).toGrpIso

/-- 同じ整数 π 比較同型は、元の実余極限余錐の各脚を誘導する。 -/
lemma sequentialLevelColimitHomotopyIso_ι (D : SpectrumSequence.{u}) (j : ℤ)
    (a : SequentialIndex.{u}) :
    colimit.ι (OmegaSpectrum.spectrumHomotopyGroupDiagram D j) a ≫
        (sequentialLevelColimitHomotopyIso D j).hom =
      GrpCat.ofHom (OmegaSpectrum.homotopyMap (sequentialLevelColimitInjection D a) j) := by
  rw [sequentialLevelColimitHomotopyIso, Iso.trans_hom, ← Category.assoc,
    OmegaSpectrum.filteredSpectrumHomotopyIso_ι]
  exact (sequentialLevelPiCoconeIso D j).hom.w a

end SerrePositivity.KST.NonConnective

module

public import SerrePositivity.KST.NonConnective.SequentialEdgePi

/-!
概要：同じ BF 候補の実 Sp 余極限余錐の各辺で、全整数 π の余極限比較を公開する。
方針：実辺から読み戻した BF 射の同じ π 作用を、既存の群余極限と照合する。
規約：実余錐・IsColimitCone・実辺の群 cocone を一つの対象で保持する。
使われ方：K-7 工程 1 の完成した逐次余極限界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 同じ候補の実余極限余錐の実辺から読み戻した π 作用の群 cocone。 -/
def sequentialCandidatePiCocone (D : SpectrumSequence.{u}) (j : ℤ) :
    Cocone (OmegaSpectrum.spectrumHomotopyGroupDiagram D j) where
  pt := GrpCat.of (OmegaSpectrum.homotopyGroup (sequentialSpectrum D) j)
  ι := {
    app a := GrpCat.ofHom (OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom D a) j)
    naturality a b f := by
      change (OmegaSpectrum.spectrumHomotopyGroupDiagram D j).map f ≫
        GrpCat.ofHom (OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom D b) j) =
          GrpCat.ofHom (OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom D a) j)
      rw [sequentialCandidateColimitLeg_pi, sequentialCandidateColimitLeg_pi]
      exact (sequentialPiCocone D j).ι.naturality f }

/-- 同じ元の注入の群余錐と、実際の余極限余錐の実辺の群余錐との同型。 -/
def sequentialCandidatePiCoconeIso (D : SpectrumSequence.{u}) (j : ℤ) :
    sequentialPiCocone D j ≅ sequentialCandidatePiCocone D j :=
  Cocone.ext (Iso.refl _) (by
    intro a
    change GrpCat.ofHom (OmegaSpectrum.homotopyMap
      (OmegaSpectrum.filteredSpectrumInjection D a) j) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact congrArg GrpCat.ofHom (sequentialCandidateColimitLeg_pi D a j).symm)

/-- 同じ BF 候補の実 Sp 余極限余錐の実辺は、全整数 π で群の余極限を与える。 -/
def sequentialCandidatePiCoconeIsColimit (D : SpectrumSequence.{u}) (j : ℤ) :
    IsColimit (sequentialCandidatePiCocone D j) :=
  IsColimit.ofIsoColimit (sequentialPiCoconeIsColimit D j) (sequentialCandidatePiCoconeIso D j)

/-- 既存の全整数 π 比較同型は、同じ実 Sp 余極限余錐の各実辺の作用を誘導する。 -/
theorem sequentialCandidateColimitHomotopyIso_ι (D : SpectrumSequence.{u}) (j : ℤ)
    (a : SequentialIndex.{u}) :
    colimit.ι (OmegaSpectrum.spectrumHomotopyGroupDiagram D j) a ≫
        (OmegaSpectrum.filteredSpectrumHomotopyIso D j).hom =
      GrpCat.ofHom (OmegaSpectrum.homotopyMap (sequentialCandidateColimitLegHom D a) j) := by
  rw [sequentialCandidateColimitLeg_pi]
  exact OmegaSpectrum.filteredSpectrumHomotopyIso_ι D j a

end SerrePositivity.KST.NonConnective

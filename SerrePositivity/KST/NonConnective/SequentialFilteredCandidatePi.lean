module
public import SerrePositivity.KST.NonConnective.FilteredExchangeHomotopyColimit
public import SerrePositivity.KST.NonConnective.SequentialFilteredExchangeInjection

/-!
概要：実 filtered BF 注入を脚とする、行ごとの逐次候補の整数 π 余極限。
方針：元の実交換射が同じ候補比較を回収する式を群余錐同型へ束ねる。
規約：同じ BF 注入を保持する群の普遍性。一般 filtered Sp 余錐とは区別する。
使われ方：K-7 e の実 filtered/逐次交換を、全整数 π の同じ余錐へ接続する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (D : J ⥤ SpectrumSequence.{u}) (c : Cocone D) (hc : IsColimit c)

include c hc in
/-- 元の行候補からの実 BF 注入を、そのまま整数 π の全脚とする。 -/
def sequentialFilteredCandidatePiCocone (j : ℤ) :
    Cocone (D ⋙ sequentialCandidatePiFunctor j ⋙ forget₂ CommGrpCat GrpCat) where
  pt := GrpCat.of (OmegaSpectrum.homotopyGroup
    (OmegaSpectrum.filteredOmegaSpectrum (sequentialFilteredLevelDiagram D)) j)
  ι := {
    app a := GrpCat.ofHom (OmegaSpectrum.homotopyMap
      (sequentialFilteredCandidateInjection D a) j)
    naturality _ _ f := by
      have h := sequentialFilteredCandidateInjection_naturality D c hc f
      rw [← sequentialCandidateMap_hom, ← SpectrumHo.hom_comp] at h
      apply ConcreteCategory.hom_ext
      intro x
      exact DFunLike.congr_fun
        ((OmegaSpectrum.homotopyMap_comp _ _ j).symm.trans
          (SpectrumHo.homotopyMap_eq_of_hom_eq _ _ h j)) x }

/-- 同じ実交換射の π 同型は、元の候補比較を脚とする群余錐への同型。 -/
def sequentialFilteredCandidatePiCoconeIso (j : ℤ) :
    sequentialFilteredCandidatePiCocone D c hc j ≅
      (sequentialCandidatePiFunctor j ⋙ forget₂ CommGrpCat GrpCat).mapCocone c :=
  Cocone.ext ((sequentialFilteredExchangeMap_piIsomorphism D c hc).groupEquiv j).toGrpIso
    (by
      intro a
      apply ConcreteCategory.hom_ext
      intro x
      exact DFunLike.congr_fun (sequentialFilteredCandidateInjection_pi D c hc a j) x)

/-- 元の行候補の実 BF 注入は、全整数 π で群余極限を与える。 -/
def sequentialFilteredCandidatePiCoconeIsColimit (j : ℤ) :
    IsColimit (sequentialFilteredCandidatePiCocone D c hc j) :=
  IsColimit.ofIsoColimit (sequentialCandidatePi_mapCoconeIsColimit_of_filtered c hc j)
    (sequentialFilteredCandidatePiCoconeIso D c hc j).symm

end SerrePositivity.KST.NonConnective

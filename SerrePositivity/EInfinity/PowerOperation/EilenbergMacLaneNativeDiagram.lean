module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneNativeHomologyIso
public import SerrePositivity.EInfinity.PowerOperation.OmegaSpectrumNativeHoComparison
public import SerrePositivity.EInfinity.PowerOperation.OrdinaryNerveHoNaturality

/-!
# 同じ全複体の native Sp 図式のホモトピー圏と π/H の全比較

DAG XIII §2.2 の π/H 自然同型への前段。通常のスペクトル関手と元の native 図式を、
同じ nerve と同じ coherent な辺で接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
local instance emNativeDiagramSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable (A : Type u) [CommRing A]

lemma eilenbergMacLaneOrdinaryNative_eq :
    eilenbergMacLaneOrdinaryNative A =
      nerveMap (eilenbergMacLaneSpectrumFunctor A) ≫ nerveToCoherent OmegaSpectrum.{u} := by
  simp only [eilenbergMacLaneOrdinaryNative, omegaSequenceNative,
    eilenbergMacLaneSpectrumFunctor]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  exact congrArg ((nerveToCoherent OmegaSpectrum.{u}).app n)
    (CategoryTheory.Functor.assoc Γ (eilenbergMacLaneOmegaSequenceFunctor A)
      omegaSequenceReplacementFunctor)

def eilenbergMacLaneNativeHoDiagramIso :
    ordinaryNerveHomotopyFunctor (Complex A) ⋙
      (hoFunctor.map (eilenbergMacLaneOrdinaryNative A)).toFunctor ≅
      eilenbergMacLaneSpectrumFunctor A ⋙ omegaSpectrumHoFunctor := by
  let N := (hoFunctor.map (nerveToCoherent OmegaSpectrum.{u})).toFunctor
  have h₁ : ordinaryNerveHomotopyFunctor (Complex A) ⋙
      (hoFunctor.map (eilenbergMacLaneOrdinaryNative A)).toFunctor ≅
      (ordinaryNerveHomotopyFunctor (Complex A) ⋙
        (hoFunctor.map (nerveMap (eilenbergMacLaneSpectrumFunctor A))).toFunctor) ⋙ N := by
    apply eqToIso
    simp only [eilenbergMacLaneOrdinaryNative_eq, Functor.map_comp, Cat.Hom.comp_toFunctor]
    rfl
  exact h₁ ≪≫ Functor.isoWhiskerRight
    (ordinaryNerveHoNaturality (eilenbergMacLaneSpectrumFunctor A)) N ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (eilenbergMacLaneSpectrumFunctor A)
        omegaSpectrumNativeHoComparison

/-- 同じ native 図式の全鎖写像に対する π_j/H^{-j} の自然同型。 -/
def eilenbergMacLaneNativeDiagramHomologyIso (j : ℤ) :
    (ordinaryNerveHomotopyFunctor (Complex A) ⋙
      (hoFunctor.map (eilenbergMacLaneOrdinaryNative A)).toFunctor) ⋙ SpectrumHo.piFunctor j ≅
      complexMultiplicativeCohomology A j :=
  Functor.isoWhiskerRight (eilenbergMacLaneNativeHoDiagramIso A) (SpectrumHo.piFunctor j) ≪≫
    eilenbergMacLaneNativeHomologyIso A j

end SerrePositivity.EInfinity.PowerOperation

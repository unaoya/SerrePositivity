module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumPostcompositionNaturality
public import SerrePositivity.KST.LocalizingInvariants.FibrationReplacementUnitPrism

/-!
概要：fibration 置換単位の相対区間を、元の射影に対する二つの全 h Fun 可換式にする。
方針：同じ後合成 prism の対角が定数であることを使い、その恒等射を相殺する。
規約：単位の全区間と両端の射影を保持。使われ方：模型比較の輸送単位の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison

local instance unitNaturalityCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def unitSourcePost := HomotopyArrow.rebase
  (SpectrumPostcomposition.sourcePost (fibrationReplacementProjection q) (unitPath p q a b h).path)
  rfl (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
    (unitFirst_projection p q a b h))

def unitTargetPost := HomotopyArrow.rebase
  (SpectrumPostcomposition.targetPost (fibrationReplacementProjection q) (unitPath p q a b h).path)
  rfl (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
    (unitSecond_projection p q a b h))

def unitSourcePre := HomotopyArrow.rebase
  (SpectrumPostcomposition.sourcePre (fibrationReplacementProjection q) (unitPath p q a b h).path)
  (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
    (unitFirst_projection p q a b h)) rfl

def unitTargetPre := HomotopyArrow.rebase
  (SpectrumPostcomposition.targetPre (fibrationReplacementProjection q) (unitPath p q a b h).path)
  (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
    (unitSecond_projection p q a b h)) rfl

lemma unitPostEdge_identity :
    Arrow.mk (SpectrumMappingPath.arrowHom
      (SpectrumMappingPath.postEdge (fibrationReplacementProjection q) (unitPath p q a b h).path)) =
    Arrow.mk (𝟙 (HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (p ≫ b)).edge)))) := by
  have hm : (SpectrumMappingPath.homotopy
      (SpectrumMappingPath.postEdge (fibrationReplacementProjection q)
        (unitPath p q a b h).path)).h =
      fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (p ≫ b)).edge :=
    (SpectrumMappingPath.postTrianglePrism_diagonal _ _).symm.trans
      (unitTrianglePrism_diagonal p q a b h)
  exact (SpectrumPostcomposition.path_arrow _).symm.trans (HomotopyArrow.identity _ _ hm)

lemma unitPost_naturality :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (unitSourcePost p q a b h)) =
    SpectrumMappingPath.arrowHom (unitPath p q a b h).path ≫
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (unitTargetPost p q a b h)) := by
  let P := fibrationReplacementProjection q
  let e := (unitPath p q a b h).path
  have hn := SpectrumPostcomposition.post_naturality P e
  have hs := HomotopyArrow.rebase_arrow (SpectrumPostcomposition.sourcePost P e) rfl
    (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
      (unitFirst_projection p q a b h))
  have ht := HomotopyArrow.rebase_arrow (SpectrumPostcomposition.targetPost P e) rfl
    (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
      (unitSecond_projection p q a b h))
  have hl := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_right_of_any_identity
    (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumPostcomposition.sourcePost P e)))
    (SpectrumMappingPath.arrowHom (SpectrumMappingPath.postEdge P e))
    (unitPostEdge_identity p q a b h)).trans hs
  apply Arrow.mk_injective
  exact hl.symm.trans ((congrArg Arrow.mk hn).trans
    (arrow_mk_comp_congr (congrArg Arrow.mk (rfl : SpectrumMappingPath.arrowHom e = _)) ht))

lemma unitPre_naturality :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (unitSourcePre p q a b h)) =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (unitTargetPre p q a b h)) := by
  let P := fibrationReplacementProjection q
  let e := (unitPath p q a b h).path
  have hn := SpectrumPostcomposition.pre_naturality P e
  have hs := HomotopyArrow.rebase_arrow (SpectrumPostcomposition.sourcePre P e)
    (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
      (unitFirst_projection p q a b h)) rfl
  have ht := HomotopyArrow.rebase_arrow (SpectrumPostcomposition.targetPre P e)
    (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge)
      (unitSecond_projection p q a b h)) rfl
  have hr := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_of_any_identity
    (SpectrumMappingPath.arrowHom (SpectrumMappingPath.postEdge P e))
    (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumPostcomposition.targetPre P e)))
    (unitPostEdge_identity p q a b h)).trans ht
  apply Arrow.mk_injective
  exact hs.symm.trans ((congrArg Arrow.mk hn).trans hr)

end SerrePositivity.KST.LocalizingInvariants.FibrationReplacementComparison

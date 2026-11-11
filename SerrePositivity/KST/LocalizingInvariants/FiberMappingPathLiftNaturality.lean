module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumPostcompositionNaturality
public import SerrePositivity.KST.LocalizingInvariants.FiberMappingPathLiftPrism

/-!
概要：指定された PathLift の全区間と元の γ を、二つの三角形比較式に接続する。
方針：射影区間の実一単体の一致と fac を使い、後合成 prism の端点を元の b へ揃える。
規約：γ の類を選び直さない。使われ方：厳密化された fiber 比較の全右辺表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
open OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FiberMapping.PathLift

local instance liftNaturalityCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y Z : OmegaSpectrum.{u}} {p : Y ⟶ Z} {a : X ⟶ Y} {b : X ⟶ Z}
  {γ : (mappingSpace X Z).Edge (vertexOfHom (a ≫ p)) (vertexOfHom b)}
  (L : PathLift p a b γ)

def targetPost := HomotopyArrow.rebase (SpectrumPostcomposition.targetPost p L.path) rfl
  (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge) L.fac)

def targetPre := HomotopyArrow.rebase (SpectrumPostcomposition.targetPre p L.path)
  (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge) L.fac) rfl

lemma projectedPath_arrow :
    Arrow.mk (SpectrumMappingPath.arrowHom (SpectrumMappingPath.postEdge p L.path)) =
      Arrow.mk (SpectrumMappingPath.arrowHom γ) := by
  exact (SpectrumPostcomposition.path_arrow _).symm.trans
    ((HomotopyArrow.congr _ _ (SpectrumMappingPath.homotopy_map_congr
      (SpectrumMappingPath.postEdge p L.path) γ L.over_edge)).trans
        (SpectrumPostcomposition.path_arrow γ))

lemma post_naturality :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumPostcomposition.sourcePost p L.path)) ≫
      SpectrumMappingPath.arrowHom γ =
    SpectrumMappingPath.arrowHom L.path ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy L.targetPost) := by
  have hn := SpectrumPostcomposition.post_naturality p L.path
  have hs := arrow_mk_comp_congr (congrArg Arrow.mk
    (rfl : Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (SpectrumPostcomposition.sourcePost p L.path)) = _)) L.projectedPath_arrow
  have ht := HomotopyArrow.rebase_arrow (SpectrumPostcomposition.targetPost p L.path) rfl
    (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge) L.fac)
  apply Arrow.mk_injective
  exact hs.symm.trans ((congrArg Arrow.mk hn).trans
    (arrow_mk_comp_congr (congrArg Arrow.mk (rfl : SpectrumMappingPath.arrowHom L.path = _)) ht))

lemma pre_naturality :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumPostcomposition.sourcePre p L.path)) =
    SpectrumMappingPath.arrowHom γ ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy L.targetPre) := by
  have hn := SpectrumPostcomposition.pre_naturality p L.path
  have ht := HomotopyArrow.rebase_arrow (SpectrumPostcomposition.targetPre p L.path)
    (congrArg (fun k ↦ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge k).edge) L.fac) rfl
  apply Arrow.mk_injective
  exact (congrArg Arrow.mk hn).trans (arrow_mk_comp_congr L.projectedPath_arrow ht)

end SerrePositivity.KST.LocalizingInvariants.FiberMapping.PathLift

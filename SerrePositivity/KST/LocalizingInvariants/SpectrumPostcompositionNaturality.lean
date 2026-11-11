module

public import SerrePositivity.KST.LocalizingInvariants.TrianglePrismNaturality
public import SerrePositivity.KST.LocalizingInvariants.HomotopyMapTransport
public import SerrePositivity.KST.LocalizingInvariants.SpectrumPostcompositionPrismFamily
public import SerrePositivity.KST.LocalizingInvariants.SpectrumMappingIntervalTriangle

/-!
概要：BF 後合成の実 prism から、三角形の前半・後半と元の区間の可換式を得る。
方針：三つの全射の面を元の区間へ同定し、動く三角形の自然性を適用する。
規約：端点三角形は同じ prism の実制限。使われ方：PathLift と単位 prism の照合。
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
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumPostcomposition

local instance postNaturalityCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance postNaturalityNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

variable {X Y Z : OmegaSpectrum.{u}} (p : Y ⟶ Z) {f g : X ⟶ Y}
  (e : (mappingSpace X Y).Edge (vertexOfHom f) (vertexOfHom g))

def prismHomotopy := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.horizontal (SpectrumMappingPath.postTrianglePrism p e)

def sourceTriangle := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.sliceMap (A := (Δ[2] : SSet.{u + 1}))
  (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫ SpectrumMappingPath.postTrianglePrism p e

def targetTriangle := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.sliceMap (A := (Δ[2] : SSet.{u + 1}))
  (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫ SpectrumMappingPath.postTrianglePrism p e

lemma first_map : (TrianglePrism.firstFace (prismHomotopy p e)).h =
    (SpectrumMappingPath.homotopy e).h := SpectrumMappingPath.postTrianglePrism_first p e

lemma diagonal_map : (TrianglePrism.diagonalFace (prismHomotopy p e)).h =
    (SpectrumMappingPath.homotopy (SpectrumMappingPath.postEdge p e)).h :=
  SpectrumMappingPath.postTrianglePrism_diagonal p e

lemma last_map : (TrianglePrism.lastFace (prismHomotopy p e)).h =
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge p).edge)).h :=
  SpectrumMappingPath.postTrianglePrism_last p e

def sourcePost := HomotopyArrow.rebase (TriangleEdge.post (sourceTriangle p e))
  (HomotopyArrow.source_eq_of_map_eq _ _ (first_map p e))
  (HomotopyArrow.source_eq_of_map_eq _ _ (diagonal_map p e))

def targetPost := HomotopyArrow.rebase (TriangleEdge.post (targetTriangle p e))
  (HomotopyArrow.target_eq_of_map_eq _ _ (first_map p e))
  (HomotopyArrow.target_eq_of_map_eq _ _ (diagonal_map p e))

def sourcePre := HomotopyArrow.rebase (TriangleEdge.pre (sourceTriangle p e))
  (HomotopyArrow.source_eq_of_map_eq _ _ (diagonal_map p e))
  (HomotopyArrow.source_eq_of_map_eq _ _ (last_map p e))

def targetPre := HomotopyArrow.rebase (TriangleEdge.pre (targetTriangle p e))
  (HomotopyArrow.target_eq_of_map_eq _ _ (diagonal_map p e))
  (HomotopyArrow.target_eq_of_map_eq _ _ (last_map p e))

lemma path_arrow :
    Arrow.mk (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (SpectrumMappingPath.homotopy e))) =
      Arrow.mk (SpectrumMappingPath.arrowHom e) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  change SSet.yonedaEquiv (curry (uncurry
    (SSet.yonedaEquiv.symm (SpectrumMappingPath.arrowEdge e).edge))) = _
  rw [curry_uncurry, Equiv.apply_symm_apply]
  rfl

lemma first_arrow : Arrow.mk (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TrianglePrism.firstFace (prismHomotopy p e)))) =
      Arrow.mk (SpectrumMappingPath.arrowHom e) :=
  (HomotopyArrow.congr _ _ (first_map p e)).trans (path_arrow e)

lemma diagonal_arrow : Arrow.mk (Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (TrianglePrism.diagonalFace (prismHomotopy p e)))) =
      Arrow.mk (SpectrumMappingPath.arrowHom (SpectrumMappingPath.postEdge p e)) :=
  (HomotopyArrow.congr _ _ (diagonal_map p e)).trans (path_arrow _)

lemma post_naturality :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (sourcePost p e)) ≫
        SpectrumMappingPath.arrowHom (SpectrumMappingPath.postEdge p e) =
    SpectrumMappingPath.arrowHom e ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (targetPost p e)) := by
  have hn := TrianglePrism.post_naturality (prismHomotopy p e)
  have hs := HomotopyArrow.rebase_arrow (TriangleEdge.post (sourceTriangle p e))
    (HomotopyArrow.source_eq_of_map_eq _ _ (first_map p e))
    (HomotopyArrow.source_eq_of_map_eq _ _ (diagonal_map p e))
  have ht := HomotopyArrow.rebase_arrow (TriangleEdge.post (targetTriangle p e))
    (HomotopyArrow.target_eq_of_map_eq _ _ (first_map p e))
    (HomotopyArrow.target_eq_of_map_eq _ _ (diagonal_map p e))
  apply Arrow.mk_injective
  exact (arrow_mk_comp_congr hs (diagonal_arrow p e)).symm.trans
    (hn.trans (arrow_mk_comp_congr (first_arrow p e) ht))

lemma pre_naturality :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (sourcePre p e)) =
    SpectrumMappingPath.arrowHom (SpectrumMappingPath.postEdge p e) ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (targetPre p e)) := by
  have hn := TrianglePrism.pre_commutation (prismHomotopy p e)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge p).edge) (last_map p e)
  have hs := HomotopyArrow.rebase_arrow (TriangleEdge.pre (sourceTriangle p e))
    (HomotopyArrow.source_eq_of_map_eq _ _ (diagonal_map p e))
    (HomotopyArrow.source_eq_of_map_eq _ _ (last_map p e))
  have ht := HomotopyArrow.rebase_arrow (TriangleEdge.pre (targetTriangle p e))
    (HomotopyArrow.target_eq_of_map_eq _ _ (diagonal_map p e))
    (HomotopyArrow.target_eq_of_map_eq _ _ (last_map p e))
  apply Arrow.mk_injective
  exact hs.symm.trans (hn.trans (arrow_mk_comp_congr (diagonal_arrow p e) ht))

end SerrePositivity.KST.LocalizingInvariants.SpectrumPostcomposition

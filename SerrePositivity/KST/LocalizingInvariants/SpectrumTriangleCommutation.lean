module

public import SerrePositivity.KST.LocalizingInvariants.CompositionTriangleCommutation
public import SerrePositivity.KST.LocalizingInvariants.TriangleEdgeNormalization
public import SerrePositivity.KST.LocalizingInvariants.SpectrumTrianglePathComparison

/-!
概要：元の Sp 三角形と標準合成三角形の二つの比較式を、実 BF 区間で表示する。
方針：相対 prism の自然性と、その対角の BF 実現が保持する全 h Fun 類を接続する。
規約：元の二単体・三辺と全比較を保持。使われ方：fiber 図式の元の右辺比較の貼合せ。
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
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleNormalization

local instance triangleCommutationCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

local instance triangleCommutationNerve : Quasicategory (SimplicialNerve OmegaSpectrum.{u}) :=
  sp_quasicategory

variable {X Y Z : OmegaSpectrum.{u}} (a : X ⟶ Y) (q : Y ⟶ Z) (s : Sp.{u} _⦋2⦌)
  (h₂ : Sp.δ 2 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge)
  (h₀ : Sp.δ 0 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge)
  (d : X ⟶ Z) (h₁ : Sp.δ 1 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge d).edge)

def sourcePost := TriangleEdge.normalizedPost s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge d).edge h₂ h₁

def sourcePre := TriangleEdge.normalizedPre s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge d).edge
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge h₁ h₀

def canonicalPost := TriangleEdge.normalizedPost (canonical a q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (a ≫ q)).edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₂
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₁

def canonicalPre := TriangleEdge.normalizedPre (canonical a q)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (a ≫ q)).edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₀

def triangleHomotopy := TriangleComparison.homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q)
  s (canonical a q) h₂ h₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₀

lemma triangleHomotopy_map : (triangleHomotopy a q s h₂ h₀).h = prism a q s h₂ h₀ :=
  TriangleComparison.homotopy_map _ _ _ _ _ _ _ _

lemma diagonalFace_arrow :
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (TrianglePrism.diagonalFace (triangleHomotopy a q s h₂ h₀)))) =
    Arrow.mk (SpectrumMappingPath.arrowHom (path a q s h₂ h₀ d h₁)) := by
  have hc := HomotopyArrow.congr
    (TrianglePrism.diagonalFace (triangleHomotopy a q s h₂ h₀))
    (diagonalHomotopy a q s h₂ h₀ d h₁)
    ((congrArg (fun k ↦ (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ k)
      (triangleHomotopy_map a q s h₂ h₀)).trans
        (diagonalHomotopy_map a q s h₂ h₀ d h₁).symm)
  exact hc.trans (congrArg Arrow.mk (path_homotopy_image a q s h₂ h₀ d h₁).symm)

lemma post_commutation :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (sourcePost a s h₂ d h₁)) ≫
        SpectrumMappingPath.arrowHom (path a q s h₂ h₀ d h₁) =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPost a q)) := by
  have hn := TriangleComparison.post_commutation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q)
    s (canonical a q) h₂ h₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₀
  have hs := TriangleEdge.normalizedPost_arrow s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge d).edge h₂ h₁
  have ht := TriangleEdge.normalizedPost_arrow (canonical a q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (a ≫ q)).edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₂
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₁
  apply Arrow.mk_injective
  exact (arrow_mk_comp_congr hs
    (diagonalFace_arrow a q s h₂ h₀ d h₁)).symm.trans (hn.trans ht)

lemma pre_commutation :
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (sourcePre q s h₀ d h₁)) =
    SpectrumMappingPath.arrowHom (path a q s h₂ h₀ d h₁) ≫
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (canonicalPre a q)) := by
  have hn := TriangleComparison.pre_commutation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q)
    s (canonical a q) h₂ h₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₂ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₀
  have hs := TriangleEdge.normalizedPre_arrow s (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge d).edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge h₁ h₀
  have ht := TriangleEdge.normalizedPre_arrow (canonical a q) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (a ≫ q)).edge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct a q).d₀
  apply Arrow.mk_injective
  exact hs.symm.trans (hn.trans
    (arrow_mk_comp_congr (diagonalFace_arrow a q s h₂ h₀ d h₁) ht))

end SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleNormalization

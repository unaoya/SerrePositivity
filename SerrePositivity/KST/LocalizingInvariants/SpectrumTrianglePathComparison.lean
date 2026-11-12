module

public import SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleNormalization
public import SerrePositivity.KST.LocalizingInvariants.SpectrumIntervalPathRealization
public import SerrePositivity.KST.LocalizingInvariants.SpectrumMappingIntervalTriangle

/-!
概要：元の Sp 三角形を保持した相対 prism の対角を、実 BF 区間で実現する。
方針：区間 Hom 内の指定射を充満忠実性で戻し、辺の関手圏で同じ射を表すことを証明する。
規約：旧 triangleEdge との厳密一致は要求しない。使われ方：元の右辺比較の全 h Fun 表示。
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

local instance trianglePathCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {X Y Z : OmegaSpectrum.{u}} (a : X ⟶ Y) (q : Y ⟶ Z) (s : Sp.{u} _⦋2⦌)
  (h₂ : Sp.δ 2 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge a).edge)
  (h₀ : Sp.δ 0 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge q).edge)
  (d : X ⟶ Z) (h₁ : Sp.δ 1 s = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge d).edge)

def pathRealization := SpectrumMappingPath.normalizedIntervalRealization d (a ≫ q)
  (Truncated.HomotopyCategory.homMk (diagonalEdge a q s h₂ h₀ d h₁).toTruncated)

def path : (mappingSpace X Z).Edge (vertexOfHom d) (vertexOfHom (a ≫ q)) :=
  (pathRealization a q s h₂ h₀ d h₁).path

lemma path_interval_image : Truncated.HomotopyCategory.homMk
    (SpectrumMappingPath.intervalEdge (path a q s h₂ h₀ d h₁)).toTruncated =
      Truncated.HomotopyCategory.homMk (diagonalEdge a q s h₂ h₀ d h₁).toTruncated :=
  (pathRealization a q s h₂ h₀ d h₁).image

lemma path_arrow_image : SpectrumMappingPath.arrowHom (path a q s h₂ h₀ d h₁) =
    Truncated.HomotopyCategory.homMk
      ((diagonalEdge a q s h₂ h₀ d h₁).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _)).toTruncated :=
  congrArg (fun k ↦ (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _)).toFunctor.map k)
    (path_interval_image a q s h₂ h₀ d h₁)

def diagonalHomotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge d).edge)
    (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (a ≫ q)).edge) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge
    ((diagonalEdge a q s h₂ h₀ d h₁).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _)).toTruncated

lemma diagonalHomotopy_map : (diagonalHomotopy a q s h₂ h₀ d h₁).h =
    (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫ prism a q s h₂ h₀ := by
  rw [prism_diagonal a q s h₂ h₀ d h₁]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

lemma path_homotopy_image : SpectrumMappingPath.arrowHom (path a q s h₂ h₀ d h₁) =
    Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (diagonalHomotopy a q s h₂ h₀ d h₁)) := by
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (diagonalHomotopy a q s h₂ h₀ d h₁) =
      ((diagonalEdge a q s h₂ h₀ d h₁).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _)).toTruncated := by
    apply Truncated.Edge.ext
    change SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm _))) = _
    rw [curry_uncurry, Equiv.apply_symm_apply]
  rw [hr]
  exact path_arrow_image a q s h₂ h₀ d h₁

end SerrePositivity.KST.LocalizingInvariants.SpectrumTriangleNormalization

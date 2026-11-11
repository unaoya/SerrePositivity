module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramNormalization
public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramRightRestriction
public import SerrePositivity.KST.LocalizingInvariants.HomotopySquareRightPresentation

/-!
概要：元の fiber 図式の指定 prism から、同じ模型群比較を頂点に持つ全図式比較を構成する。
方針：元の nativeRightMappingPath を保持する全正方形比較を、同じ正規化の間の射として使う。
規約：normalizedHom との一致は後続。使われ方：その全右辺の同定から元の接続射へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

local instance diagramModelComparisonCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

lemma vertex_map_evaluate (i j : Fin 2) : (vertex i j).map f = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate f
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorCellToNatTrans_app_eq_evaluate f _

def modelComparison : normalized D ⟶ normalized E :=
  HomotopySquareFiberComparison.squareHom (NativeFiber.rightMap D.triangle)
    (NativeFiber.rightMap E.triangle) (comparisonMap f 1 0) (comparisonMap f 1 1)
    (nativeRightMappingPath f)

lemma modelComparison_right : Arrow.mk (rightRestriction.map (modelComparison f)) =
    Arrow.mk (HomotopySquareFiberComparison.rightPresentation (NativeFiber.rightMap D.triangle)
      (NativeFiber.rightMap E.triangle) (comparisonMap f 1 0) (comparisonMap f 1 1)
      (nativeRightMappingPath f)) :=
  HomotopySquareFiberComparison.squareHom_right_presentation _ _ _ _ _

lemma modelComparison_fiber_pi (j : ℤ) :
    Arrow.mk ((SpectrumHo.piFunctor j).map ((vertex 0 0).map (modelComparison f))) =
    Arrow.mk ((SpectrumHo.piComparison
      (OmegaSpectrum.homotopyFiber (NativeFiber.rightMap D.triangle)) j).hom ≫
      CommGrpCat.ofHom (modelGroupMap f j) ≫
      (SpectrumHo.piComparison
        (OmegaSpectrum.homotopyFiber (NativeFiber.rightMap E.triangle)) j).inv) := by
  rw [vertex_map_evaluate]
  exact HomotopySquareFiberComparison.squareHom_apex_pi _ _ _ _ _ j

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram

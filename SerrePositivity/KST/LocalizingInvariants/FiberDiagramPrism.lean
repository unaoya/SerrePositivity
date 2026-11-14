module

public import SerrePositivity.KST.LocalizingInvariants.FiberDiagramCategory
public import SerrePositivity.KST.LocalizingInvariants.SpectrumEdgePi
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：fiber 図式の任意の射を、元の射の類を保持する正方形の prism で表す。
方針：h Fun の辺代表を選び、頂点成分を元の評価射と整数 π の作用へ戻す。
規約：四辺の h Sp 上の可換式で prism を置き換えない。
使われ方：任意の fiber 図式比較への接続射の自然性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberDiagram

variable {D E : FiberDiagram.{u}} (f : D ⟶ E)

def comparisonHomotopy : SSet.Homotopy D.triangle.square E.triangle.square :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy f

lemma comparisonHomotopy_hom : Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (comparisonHomotopy f)) = f :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom f

def comparisonEdge (i j : Fin 2) :
    Sp.Edge (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex D.triangle.square i j) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex E.triangle.square i j) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (comparisonHomotopy f)
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)

lemma comparisonEdge_hom (i j : Fin 2) : Truncated.HomotopyCategory.homMk
    (comparisonEdge f i j).toTruncated = (vertex i j).map f := by
  rw [comparisonEdge, comparisonHomotopy, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_component]
  symm
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorCellToNatTrans_app_eq_evaluate f
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)

def comparisonMap (i j : Fin 2) :
    SpectrumHo.spectrum ((vertex i j).obj D) ⟶
      SpectrumHo.spectrum ((vertex i j).obj E) :=
  SpectrumHo.edgeMap (comparisonEdge f i j)

lemma comparisonMap_hom (i j : Fin 2) :
    SpectrumHo.hom (comparisonMap f i j) = SpectrumHo.normalize ((vertex i j).map f) := by
  rw [comparisonMap, SpectrumHo.edgeMap_hom, comparisonEdge_hom]

lemma comparisonMap_pi (i j : Fin 2) (k : ℤ) :
    SpectrumHo.piMap ((vertex i j).map f) k =
      OmegaSpectrum.homotopyMap (comparisonMap f i j) k := by
  rw [← comparisonEdge_hom f i j]
  exact SpectrumHo.piMap_edge (comparisonEdge f i j) k

end SerrePositivity.KST.LocalizingInvariants.FiberDiagram

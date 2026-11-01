module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedRowSimplexDiagram
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedDiagramGeneratorTransport
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedRowFactorization

/-!
# 元の全行の因子化図式と全単体作用素

概要：接頭列・生成矢・残り・元の列の自然変換全体が、全単体作用素に両立する。
方針：基準行の生成矢の移送、切断図式の前合成の等式、自然変換の再添字を合成する。
規約：端点の表示も含む異種等式で、元の全行・全縦射を保持する。
使われ方：hammock の分割を単体集合の射にするための整合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)
  (hθ : column W (((graph W.paths w X Y).map θ τ).obj 0) i ≠ [])

lemma rowPrefix_simplex :
    HEq (rowPrefix W ((graph W.paths w X Y).map θ τ) i hθ)
      (Functor.whiskerLeft (rowIndex θ) (rowPrefix W τ i h)) := by
  exact (ColumnCut.prefixDiagram_changeGenerator W w X Y i
    (rowGenerator_simplex W τ i h θ hθ)
    (rowCutDiagram W ((graph W.paths w X Y).map θ τ) i hθ)).symm.trans
      ((ColumnCut.prefixDiagram_congr W w X Y i (rowCutDiagram_simplex W τ i h θ hθ)).trans
        (heq_of_eq (ColumnCut.prefixDiagram_precomp W w X Y i (rowGenerator W τ i h)
          (rowIndex θ) (rowCutDiagram W τ i h))))

lemma rowGeneratorMap_simplex :
    HEq (rowGeneratorMap W ((graph W.paths w X Y).map θ τ) i hθ)
      (Functor.whiskerLeft (rowIndex θ) (rowGeneratorMap W τ i h)) := by
  exact (ColumnCut.generatorDiagram_changeGenerator W w X Y i
    (rowGenerator_simplex W τ i h θ hθ)
    (rowCutDiagram W ((graph W.paths w X Y).map θ τ) i hθ)).symm.trans
      ((ColumnCut.generatorDiagram_congr W w X Y i (rowCutDiagram_simplex W τ i h θ hθ)).trans
        (heq_of_eq (ColumnCut.generatorDiagram_precomp W w X Y i (rowGenerator W τ i h)
          (rowIndex θ) (rowCutDiagram W τ i h))))

lemma rowResidual_simplex :
    HEq (rowResidual W ((graph W.paths w X Y).map θ τ) i hθ)
      (Functor.whiskerLeft (rowIndex θ) (rowResidual W τ i h)) := by
  exact (ColumnCut.residualDiagram_changeGenerator W w X Y i
    (rowGenerator_simplex W τ i h θ hθ)
    (rowCutDiagram W ((graph W.paths w X Y).map θ τ) i hθ)).symm.trans
      ((ColumnCut.residualDiagram_congr W w X Y i (rowCutDiagram_simplex W τ i h θ hθ)).trans
        (heq_of_eq (ColumnCut.residualDiagram_precomp W w X Y i (rowGenerator W τ i h)
          (rowIndex θ) (rowCutDiagram W τ i h))))

lemma rowColumn_simplex :
    HEq (rowColumn W ((graph W.paths w X Y).map θ τ) i hθ)
      (Functor.whiskerLeft (rowIndex θ) (rowColumn W τ i h)) := by
  exact (ColumnCut.columnDiagram_changeGenerator W w X Y i
    (rowGenerator_simplex W τ i h θ hθ)
    (rowCutDiagram W ((graph W.paths w X Y).map θ τ) i hθ)).symm.trans
      ((ColumnCut.columnDiagram_congr W w X Y i (rowCutDiagram_simplex W τ i h θ hθ)).trans
        (heq_of_eq (ColumnCut.columnDiagram_precomp W w X Y i (rowGenerator W τ i h)
          (rowIndex θ) (rowCutDiagram W τ i h))))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators

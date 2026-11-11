module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRowSimplexDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedDiagramGeneratorTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedRowFactorization

/-!
# 元の全行の因子化図式と全単体作用素

概要：接頭列・生成矢・残り・元の列の自然変換全体が、全単体作用素に両立する。
方針：基準行の生成矢の移送、切断図式の前合成の等式、自然変換の再添字を合成する。
規約：端点の表示も含む異種等式で、元の全行・全縦射を保持する。
使われ方：hammock の分割を単体集合の射にするための整合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)
  (hθ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) i ≠ [])

lemma rowPrefix_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowPrefix W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)
      (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowPrefix W τ i h)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixDiagram_changeGenerator W w X Y i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator_simplex W τ i h θ hθ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)).symm.trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixDiagram_congr W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram_simplex W τ i h θ hθ)).trans
        (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.prefixDiagram_precomp W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W τ i h))))

lemma rowGeneratorMap_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGeneratorMap W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)
      (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGeneratorMap W τ i h)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorDiagram_changeGenerator W w X Y i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator_simplex W τ i h θ hθ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)).symm.trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorDiagram_congr W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram_simplex W τ i h θ hθ)).trans
        (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.generatorDiagram_precomp W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W τ i h))))

lemma rowResidual_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowResidual W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)
      (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowResidual W τ i h)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualDiagram_changeGenerator W w X Y i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator_simplex W τ i h θ hθ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)).symm.trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualDiagram_congr W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram_simplex W τ i h θ hθ)).trans
        (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.residualDiagram_precomp W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W τ i h))))

lemma rowColumn_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowColumn W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)
      (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowColumn W τ i h)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnDiagram_changeGenerator W w X Y i
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator_simplex W τ i h θ hθ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)).symm.trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.columnDiagram_congr W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram_simplex W τ i h θ hθ)).trans
        (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.columnDiagram_precomp W w X Y i (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ i h)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowCutDiagram W τ i h))))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

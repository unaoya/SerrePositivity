module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport

/-!
# 因子化図式の生成矢の表示の移送

概要：同じ生成矢の表示を移しても、接頭列・生成矢・残り・元の列の図式は同じである。
方針：生成矢や関手の等式で帰納し、元の図式の異種等式を得る。
規約：端点を含む図式全体を照合し、成分だけの一致で置き換えない。
使われ方：全単体作用素への因子化図式の整合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uI vI
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
  (X Y : Paths C) (i : Fin w.length) {I : Type uI} [Category.{vI} I]
  {a b : Quiver.Total C}

lemma prefixDiagram_congr {F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a} (h : F = G) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.prefixDiagram W w X Y i a F) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.prefixDiagram W w X Y i a G) := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixDiagram_congr)


lemma prefixDiagram_changeGenerator (h : a = b) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.prefixDiagram W w X Y i b (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport.changeGenerator W w X Y i h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.prefixDiagram W w X Y i a F) := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (prefixDiagram_changeGenerator)


lemma generatorDiagram_congr {F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a} (h : F = G) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.generatorDiagram W w X Y i a F) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.generatorDiagram W w X Y i a G) := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (generatorDiagram_congr)


lemma generatorDiagram_changeGenerator (h : a = b) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.generatorDiagram W w X Y i b (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport.changeGenerator W w X Y i h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.generatorDiagram W w X Y i a F) := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (generatorDiagram_changeGenerator)


lemma residualDiagram_congr {F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a} (h : F = G) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.residualDiagram W w X Y i a F) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.residualDiagram W w X Y i a G) := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualDiagram_congr)


lemma residualDiagram_changeGenerator (h : a = b) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.residualDiagram W w X Y i b (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport.changeGenerator W w X Y i h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.residualDiagram W w X Y i a F) := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (residualDiagram_changeGenerator)


lemma columnDiagram_congr {F G : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a} (h : F = G) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.columnDiagram W w X Y i a F) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.columnDiagram W w X Y i a G) := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (columnDiagram_congr)


lemma columnDiagram_changeGenerator (h : a = b) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut W w X Y i a) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.columnDiagram W w X Y i b (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutGeneratorTransport.changeGenerator W w X Y i h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedColumnDiagramFactorization.columnDiagram W w X Y i a F) := by
  cases h
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColumnCut export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (columnDiagram_changeGenerator)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

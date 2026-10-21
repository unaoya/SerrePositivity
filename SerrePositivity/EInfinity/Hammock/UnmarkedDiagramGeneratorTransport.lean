module

public import SerrePositivity.EInfinity.Hammock.UnmarkedColumnDiagramFactorization
public import SerrePositivity.EInfinity.Hammock.UnmarkedCutGeneratorTransport

/-!
# 因子化図式の生成矢の表示の移送

概要：同じ生成矢の表示を移しても、接頭列・生成矢・残り・元の列の図式は同じである。
方針：生成矢や関手の等式で帰納し、元の図式の異種等式を得る。
規約：端点を含む図式全体を照合し、成分だけの一致で置き換えない。
使われ方：全単体作用素への因子化図式の整合。
-/

@[expose] public section
universe u v uI vI
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.ColumnCut
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (w : Word)
  (X Y : Paths C) (i : Fin w.length) {I : Type uI} [Category.{vI} I]
  {a b : Quiver.Total C}

lemma prefixDiagram_congr {F G : I ⥤ ColumnCut W w X Y i a} (h : F = G) :
    HEq (prefixDiagram W w X Y i a F) (prefixDiagram W w X Y i a G) := by
  cases h
  rfl

lemma prefixDiagram_changeGenerator (h : a = b) (F : I ⥤ ColumnCut W w X Y i a) :
    HEq (prefixDiagram W w X Y i b (F ⋙ changeGenerator W w X Y i h))
      (prefixDiagram W w X Y i a F) := by
  cases h
  rfl

lemma generatorDiagram_congr {F G : I ⥤ ColumnCut W w X Y i a} (h : F = G) :
    HEq (generatorDiagram W w X Y i a F) (generatorDiagram W w X Y i a G) := by
  cases h
  rfl

lemma generatorDiagram_changeGenerator (h : a = b) (F : I ⥤ ColumnCut W w X Y i a) :
    HEq (generatorDiagram W w X Y i b (F ⋙ changeGenerator W w X Y i h))
      (generatorDiagram W w X Y i a F) := by
  cases h
  rfl

lemma residualDiagram_congr {F G : I ⥤ ColumnCut W w X Y i a} (h : F = G) :
    HEq (residualDiagram W w X Y i a F) (residualDiagram W w X Y i a G) := by
  cases h
  rfl

lemma residualDiagram_changeGenerator (h : a = b) (F : I ⥤ ColumnCut W w X Y i a) :
    HEq (residualDiagram W w X Y i b (F ⋙ changeGenerator W w X Y i h))
      (residualDiagram W w X Y i a F) := by
  cases h
  rfl

lemma columnDiagram_congr {F G : I ⥤ ColumnCut W w X Y i a} (h : F = G) :
    HEq (columnDiagram W w X Y i a F) (columnDiagram W w X Y i a G) := by
  cases h
  rfl

lemma columnDiagram_changeGenerator (h : a = b) (F : I ⥤ ColumnCut W w X Y i a) :
    HEq (columnDiagram W w X Y i b (F ⋙ changeGenerator W w X Y i h))
      (columnDiagram W w X Y i a F) := by
  cases h
  rfl

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.ColumnCut

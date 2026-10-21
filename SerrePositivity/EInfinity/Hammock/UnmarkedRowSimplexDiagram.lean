module

public import SerrePositivity.EInfinity.Hammock.UnmarkedRowSimplexGenerator
public import SerrePositivity.EInfinity.Hammock.UnmarkedColumnDiagramFactorization

/-!
# 元の全行の切断図式の単体作用素への整合

概要：元の任意の単体作用素で制限した切断図式は、生成矢の表示を移すと元の前合成に一致。
方針：基準行の生成矢の等式と固定切断の一意性を使う。
規約：全行・全縦射・元の nerve の作用素を厳密に保持する。
使われ方：hammock の分割の単体的自然性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)

def rowIndex : Fin (m.unop.len + 1) ⥤ Fin (n.unop.len + 1) := θ.unop.toOrderHom.toFunctor

lemma rowCutDiagram_simplex
    (hθ : column W (((graph W.paths w X Y).map θ τ).obj 0) i ≠ []) :
    rowCutDiagram W ((graph W.paths w X Y).map θ τ) i hθ ⋙
      ColumnCut.changeGenerator W w X Y i (rowGenerator_simplex W τ i h θ hθ) =
        rowIndex θ ⋙ rowCutDiagram W τ i h := by
  let hg := rowGenerator_simplex W τ i h θ hθ
  change ColumnCut.lift W w X Y i (rowGenerator W τ i h) (rowIndex θ ⋙ τ)
      (fun k => hg ▸ fixedRowCut W ((graph W.paths w X Y).map θ τ) i hθ k) =
        rowIndex θ ⋙ ColumnCut.lift W w X Y i (rowGenerator W τ i h) τ (fixedRowCut W τ i h)
  rw [← ColumnCut.lift_precomp]
  exact ColumnCut.lift_ext W w X Y i (rowGenerator W τ i h) _ _ _

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators

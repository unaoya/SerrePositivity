module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedFirstColumn
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagColumnSplitRecovery
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramOfFunctor

/-!
# 最初の非指定列より前の元の全語の指定性

概要：元の全行から切り出した prefix の全列と全縦射は元の指定射列である。
方針：列の最小性、全行の不変性、元の切断の列の回収を使う。
規約：前の語が空の場合も含み、元の図式の端点と縦成分を保持する。
使われ方：非指定生成矢の前の W-hammock の構成。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (h0 : ∃ j, column W (τ.obj 0) j ≠ [])

def beforeFirstColumn := Zigzag.MovingDiagram.ColumnSplit.before
  (firstColumn W (τ.obj 0) h0) (Zigzag.MovingDiagram.ofFunctor τ)

lemma beforeFirstColumn_arrow_mem (k : Fin (n.unop.len + 1))
    (j : Fin (Word.ColumnSplit.before w (firstColumn W (τ.obj 0) h0)).length) :
    W.paths (((beforeFirstColumn W τ h0).obj k).arrow j) := by
  apply Zigzag.MovingDiagram.ColumnSplit.before_arrow_mem
  apply before_firstColumn_row_mem W τ h0 k
  change j.val < (firstColumn W (τ.obj 0) h0).val
  exact j.isLt

lemma beforeFirstColumn_map_mem {k l : Fin (n.unop.len + 1)} (f : k ⟶ l)
    (j : Fin ((Word.ColumnSplit.before w (firstColumn W (τ.obj 0) h0)).length + 1)) :
    W.paths (((beforeFirstColumn W τ h0).map f).app j) :=
  ((beforeFirstColumn W τ h0).map f).app_mem j

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators

module

public import SerrePositivity.EInfinity.Hammock.UnmarkedCutAttachmentDiagrams
public import SerrePositivity.EInfinity.Hammock.UnmarkedFirstColumnPrefix
public import SerrePositivity.EInfinity.Hammock.ZigzagAppendArrowProperty

/-!
# 最初の非指定生成矢の始域までの指定 prefix

概要：元の前の全語と列内部の指定接頭射を接続し、全列・全縦射が指定であることを証明する。
方針：最初の列の最小性と元の連結の列の性質の回収を使う。
規約：固定端点の実際の関手を構成し、空の前の語も含む。
使われ方：指定部分圏の W-hammock への回収。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AttachedPrefix
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (h0 : ∃ j, column W (τ.obj 0) j ≠ [])

abbrev index := firstColumn W (τ.obj 0) h0

lemma nonempty : column W (τ.obj 0) (index W τ h0) ≠ [] := firstColumn_nonempty W (τ.obj 0) h0

def diagram := Attachments.prefixDiagram W τ (index W τ h0) (nonempty W τ h0)

def functor := (diagram W τ h0).fixedFunctor

lemma arrow_mem (k : Fin (n.unop.len + 1))
    (j : Fin (Word.append (Word.ColumnSplit.before w (index W τ h0))
      (Word.single .forward)).length) : W.paths (((diagram W τ h0).obj k).arrow j) := by
  change W.paths ((ZigzagAppend.obj
    ((Attachments.beforeDiagram W τ (index W τ h0)).obj k)
    ((Attachments.leftBlock W τ (index W τ h0) (nonempty W τ h0)).obj k)).arrow j)
  cases j using Fin.addCases with
  | left j =>
    apply (ZigzagAppend.arrow_left_property W.paths _ _ j).2
    exact beforeFirstColumn_arrow_mem W τ h0 k j
  | right j =>
    apply (ZigzagAppend.arrow_right_property W.paths _ _ j).2
    exact Attachments.leftBlock_arrow_mem W τ (index W τ h0) (nonempty W τ h0) k j

lemma map_mem {k l : Fin (n.unop.len + 1)} (f : k ⟶ l)
    (j : Fin ((Word.append (Word.ColumnSplit.before w (index W τ h0))
      (Word.single .forward)).length + 1)) : W.paths (((diagram W τ h0).map f).app j) :=
  ((diagram W τ h0).map f).app_mem j

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AttachedPrefix

module

public import SerrePositivity.EInfinity.Hammock.UnmarkedRowCutDiagram

/-!
# 元の一文字の列からの同じ Total 生成矢の回収

概要：非指定列の消去が一文字なら、選択した元の生成矢はその文字自身である。
方針：元の firstCut_erasure の先頭を取る。
規約：元の全対象・元の射を持つ Total 矢を回収する。
使われ方：貼り戻しの後の同じ生成矢の回収。
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

lemma rowGenerator_of_singleton (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
    (hi : column W (τ.obj 0) i ≠ []) (g : Quiver.Total C)
    (hc : column W (τ.obj 0) i = [g]) : rowGenerator W τ i hi = g := by
  have he := GeneratorWord.firstCut_erasure W (rowFirstCut W τ i hi 0)
  exact (Option.some.inj (congrArg List.head? (hc.symm.trans he))).symm

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators

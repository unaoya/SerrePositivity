module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedValueAppend
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstColumn
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendArrowProperty

/-!
# 元の三因子を貼った語の最初の非指定列

概要：全指定 prefix・元の一生成矢・任意の残りを貼った語の最小非指定位置を回収する。
方針：元の左右の列の回収と firstColumn の最小性を使う。
規約：空の prefix と残りの語も含む。
使われ方：貼り戻しの後の抽出による同じ生成矢と元の因子の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)
  (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths a X g.val.left) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths b g.val.right Y)

def obj := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W.paths) g.val.hom.toPath)) T

def columnIndex (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) b).length :=
  ((0 : Fin 1).natAdd a.length).castAdd b.length

lemma column_generator : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.obj W g S T) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.columnIndex a b) = [g.val] := by
  classical
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.obj, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.columnIndex, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.column_append_left, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.column_append_right]
  change (if W g.val.hom then [] else [] ++ [g.val]) = _
  rw [ite_eq_right g.property]
  rfl

lemma before_column_mem (hs : ∀ j, W.paths (S.arrow j))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) b).length)
    (hj : j < _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.columnIndex a b) : W.paths ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.obj W g S T).arrow j) := by
  have hjv : j.val < a.length := hj
  let i : Fin a.length := ⟨j.val, hjv⟩
  have he : j = (i.castAdd 1).castAdd b.length := Fin.ext rfl
  cases he
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_left_property W.paths _ _ _).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_left_property W.paths S
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W.paths) g.val.hom.toPath) i)).2 (hs i)

lemma firstColumn_eq (hs : ∀ j, W.paths (S.arrow j))
    (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.obj W g S T) j ≠ []) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.obj W g S T) h = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.columnIndex a b := by
  apply le_antisymm
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_le W _ h _ (fun he => List.cons_ne_nil _ _
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.column_generator W g S T).symm.trans he))
  · by_contra hn
    have hlt := lt_of_not_ge hn
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W _ h (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.erase_marked W _
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted.before_column_mem W g S T hs _ hlt))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.Pasted

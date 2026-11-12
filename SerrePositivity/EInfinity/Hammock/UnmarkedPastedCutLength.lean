module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneratorWordFixedCutLength

/-!
# 元の貼り戻しの一文字の列の全行の切断の前後の長さ

概要：元の三因子を貼った生成列の raw な射列は長さ一で、全行の切断の前後は長さ零である。
方針：元の左右の列への任意の射の性質の移送と FixedCut の因子化を使う。
規約：消去後の長さだけでなく元の射列自身の長さを使う。
使われ方：元の prefix・残りの点を恒等列の挿入へ照合する。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)

lemma column_length_one (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths a X g.val.left)
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W.paths b g.val.right Y) : ((obj W g S T).arrow (columnIndex a b)).length = 1 := by
  let L : MorphismProperty (Paths C) := fun _ _ p => p.length = 1
  exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_left_property L _ _ _).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_right_property L S
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W.paths) g.val.hom.toPath) (0 : Fin 1))).2 rfl

variable (σ : (AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths b g.val.right Y).obj n)
  (h : ∃ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((simplex W g σ τ).obj 0) j ≠ [])

lemma selected_column_length_one (d : Fin (n.unop.len + 1)) :
    (((simplex W g σ τ).obj d).arrow (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h)).length = 1 :=
  (congrArg (fun j => (((simplex W g σ τ).obj d).arrow j).length)
    (simplex_firstColumn W g σ τ h)).trans
      (column_length_one W g (((AllMarked.graphMap W X g.val.left a).app n σ).obj d) (τ.obj d))

lemma cut_left_length_zero (d : Fin (n.unop.len + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W (simplex W g σ τ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h) d).left.length = 0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut.left_length_of_one W _ (selected_column_length_one W g σ τ h d)

lemma cut_right_length_zero (d : Fin (n.unop.len + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W (simplex W g σ τ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.index W (simplex W g σ τ) h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachedPrefix.nonempty W _ h) d).right.length = 0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedCut.right_length_of_one W _ (selected_column_length_one W g σ τ h d)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted

module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineFoldUnique

/-!
# 元の因子列の普遍的な評価と目標の関手

概要：評価の目標の関手を前後で適用した結果は同じ元の因子列で一致する。
方針：目標の関手の単位・合成保存を普遍データへ移し、元の列で帰納する。
規約：元の指定因子と元の生成矢の像を保持する。
使われ方：単体的な目標の各作用素との評価の整合。
-/

@[expose] public section
universe u uD vD uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {n : SimplexCategoryᵒᵖ}
  {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  (F : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData W n D) (K : D ⥤ E)

def mapTarget : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData W n E where
  obj X := K.obj (F.obj X)
  marked p := K.map (F.marked p)
  generator g := K.map (F.generator g)
  marked_unit X := by rw [F.marked_unit, K.map_id]
  marked_comp p q := by rw [F.marked_comp, K.map_comp]

lemma fold_target {X Y : Paths C} (t : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine W Y n X) :
    (F.mapTarget K).fold t = K.map (F.fold t) := by
  induction t with
  | nil X p => rfl
  | cons X g p t ih =>
    change K.map (F.marked p) ≫ K.map (F.generator g) ≫ (F.mapTarget K).fold t =
      K.map (F.marked p ≫ F.generator g ≫ F.fold t)
    rw [ih, K.map_comp, K.map_comp]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData

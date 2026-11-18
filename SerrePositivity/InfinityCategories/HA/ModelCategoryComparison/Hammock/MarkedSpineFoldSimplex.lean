module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.MarkedSpineFoldUnique

/-!
# 元の因子列の普遍的な評価と全単体作用素

概要：指定因子の元の単体作用を前合成した評価は、全因子列の再添字と一致する。
方針：指定合成と単位の単体的自然性を普遍データへ移し、元の列で帰納する。
規約：非指定生成矢は同じ元の矢に固定する。
使われ方：次数ごとの自由積の普遍性を単体的に結合する。
-/

@[expose] public section
universe u uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData
open _root_.CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {n m : SimplexCategoryᵒᵖ}
  {D : Type uD} [Category.{vD} D] (F : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData W m D)

def precompSimplex (θ : n ⟶ m) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData W n D where
  obj := F.obj
  marked {X Y} p := F.marked ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeSpace W X Y).map θ p)
  generator := F.generator
  marked_unit X := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeUnitPoint_simplex]
    exact F.marked_unit X
  marked_comp p q := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.AllMarked.nativeComposePoint_simplex]
    exact F.marked_comp _ _

lemma fold_simplex (θ : n ⟶ m) {X Y : Paths C} (t : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine W Y n X) :
    (F.precompSimplex θ).fold t = F.fold (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.map θ t) := by
  induction t with
  | nil X p => rfl
  | cons X g p t ih =>
    exact congrArg (fun r => F.marked ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).map θ p) ≫
      F.generator g ≫ r) ih

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine.FoldData

module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineCompositionLaws

/-!
# 元の非指定生成矢の因子列と全 cons の三因子分解

概要：指定単位二点を両端に持つ元の生成矢の因子列を構成する。
方針：貼り戻しの単射性と元の左右単位則・結合則を使う。
規約：元の生成矢の同じ一文字の射列を保持する。
使われ方：指定因子と非指定生成矢からの拡張の一意性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {X Y : Paths C} {n : SimplexCategoryᵒᵖ}

def generatorPoint (W : MorphismProperty C) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (n : SimplexCategoryᵒᵖ) :
    MarkedSpine W g.val.right n g.val.left :=
  cons g.val.left g (AllMarked.nativeUnitPoint W g.val.left n) (unitPoint W g.val.right n)

lemma glue_generatorPoint (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) :
    glue (generatorPoint W g n) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W.paths g.val.hom.toPath n := by
  change FactorTarget.pastePoint W g.val.left g.val.right g
    (AllMarked.nativeUnitPoint W g.val.left n) (glue (unitPoint W g.val.right n)) = _
  dsimp only [FactorTarget.pastePoint]
  rw [AllMarked.inclusion_unitPoint, glue_unit, ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint_identity,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint_identity, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_identity_left, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_identity_right]

lemma generatorPoint_simplex {m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) :
    map θ (generatorPoint W g n) = generatorPoint W g m := by
  apply glue_injective
  rw [glue_simplex, glue_generatorPoint, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint_simplex, glue_generatorPoint]

lemma cons_decomposition (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.left W X g.val).obj n)
    (t : MarkedSpine W Y n g.val.right) :
    cons X g p t = append (nil X p) (append (generatorPoint W g n) t) := by
  apply glue_injective
  rw [glue_append, glue_append, glue_generatorPoint]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_assoc W.paths _ _ _

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine

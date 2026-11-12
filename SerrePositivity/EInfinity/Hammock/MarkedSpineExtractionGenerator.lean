module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineExtractionComposition

/-!
# 元の非指定生成矢の単体写像の抽出

概要：元の生成矢の標準射を抽出すると同じ元の生成因子列へ戻る。
方針：元の貼り戻しによる生成矢の回収と逆向きの恒等式を使う。
規約：元の射の一定単体と全次数を保持する。
使われ方：元の hammock の豊穣自由積の生成矢の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

lemma extraction_arrowMap (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W.paths g.val.hom.toPath ≫ extraction W g.val.right g.val.left =
      MarkedSpine.generatorMap W g := by
  rw [← generatorMap_gluing, Category.assoc, gluing_extraction, Category.comp_id]

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor

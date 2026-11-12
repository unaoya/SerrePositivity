module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineEnrichedFoldUnique
public import SerrePositivity.EInfinity.Hammock.MarkedSpineExtractionGenerator

/-!
# 元の自由圏の hammock から任意の豊穣目標への拡張

概要：元の指定 hammock と非指定生成矢の像から元の hammock 自身への拡張を構成する。
方針：元の抽出の後で普遍的な因子列の評価を適用する。
規約：元の全語の余極限・元の単位・元の合成を保持する。
使われ方：DK 命題3.2の元の自由積の豊穣普遍性。
-/

@[expose] public section
universe u uD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
namespace EnrichedFoldData
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{u} C] {W : MorphismProperty C}
  {D : Type uD} [EnrichedCategory SSet.{u} D] (F : EnrichedFoldData W D)

def hammockFoldMap (X Y : Paths C) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y ⟶ F.obj X ⟶[SSet.{u}] F.obj Y :=
  extraction W Y X ≫ F.foldMap X Y

lemma hammockFoldMap_marked (X Y : Paths C) :
    AllMarked.inclusion W X Y ≫ F.hammockFoldMap X Y = F.marked X Y := by
  rw [hammockFoldMap, ← Category.assoc, nativeInclusion_extraction, foldMap_marked]

lemma hammockFoldMap_generator (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W.paths g.val.hom.toPath ≫ F.hammockFoldMap g.val.left g.val.right =
      F.generator g := by
  rw [hammockFoldMap, ← Category.assoc, extraction_arrowMap, foldMap_generator]

lemma hammockFoldMap_unit (X : Paths C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W.paths X ≫ F.hammockFoldMap X X = eId SSet.{u} (F.obj X) := by
  rw [hammockFoldMap, ← Category.assoc, extraction_unitMap, foldMap_unit]

lemma hammockFoldMap_comp (X Y Z : Paths C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W.paths X Y Z ≫ F.hammockFoldMap X Z =
      (F.hammockFoldMap X Y ⊗ₘ F.hammockFoldMap Y Z) ≫
        eComp SSet.{u} (F.obj X) (F.obj Y) (F.obj Z) := by
  dsimp only [hammockFoldMap]
  rw [← Category.assoc, extraction_composition, Category.assoc, foldMap_comp,
    ← Category.assoc, tensorHom_comp_tensorHom]

end EnrichedFoldData
end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine

module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeGraphDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph
public import SerrePositivity.EInfinity.Hammock.ReducedColimit

/-!
# 相対関手による元の hammock 余極限と縮約済み単体集合の写像

概要：元の全語の比較を余極限へ移し、既存の縮約同型で同じ hammock の写像を得る。
方針：元の標準射の自然性を保持し、縮約への同型を前後に合成する。
規約：元の正規化と元の augmentation との整合性を明示する。
使われ方：自由相対解像の比較と元の reduced hammock の接続。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Relative
open CategoryTheory CategoryTheory.Limits

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) (X Y : C)

def colimitMap : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph V (F.functor.obj X) (F.functor.obj Y) :=
  colim.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap F X Y)

lemma graphInclusion_colimitMap (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫ colimitMap F X Y =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap F X Y).app w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (F.functor.obj Y) w :=
  colimit.ι_map _ _

def reducedMap : reducedSimplicialSet W X Y ⟶
    reducedSimplicialSet V (F.functor.obj X) (F.functor.obj Y) :=
  (reducedColimitIso W X Y).inv ≫ colimitMap F X Y ≫
    (reducedColimitIso V (F.functor.obj X) (F.functor.obj Y)).hom

lemma reducedMap_augmentation : reducedMap F X Y ≫
    reducedAugmentation V (F.functor.obj X) (F.functor.obj Y) =
      reducedAugmentation W X Y ≫ colimitMap F X Y := by
  simp only [reducedMap, ← reducedColimitIso_inv, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

lemma graphNormalization_reducedMap (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    graphNormalization W X Y w ≫ reducedMap F X Y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap F X Y).app w ≫
        graphNormalization V (F.functor.obj X) (F.functor.obj Y) w := by
  rw [← reducedColimitIso_hom_fac W X Y w]
  dsimp only [reducedMap]
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, graphInclusion_colimitMap,
    Category.assoc, reducedColimitIso_hom_fac]

end SerrePositivity.EInfinity.Hammock.Relative

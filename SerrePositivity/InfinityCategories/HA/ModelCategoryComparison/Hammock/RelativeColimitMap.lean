module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeGraphDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ReducedColimit

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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative
open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) (X Y : C)

def colimitMap : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph V (F.functor.obj X) (F.functor.obj Y) :=
  colim.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap F X Y)

lemma graphInclusion_colimitMap (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap F X Y).app w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion V (F.functor.obj X) (F.functor.obj Y) w :=
  colimit.ι_map _ _

def reducedMap : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Y ⟶
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet V (F.functor.obj X) (F.functor.obj Y) :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W X Y).inv ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y ≫
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso V (F.functor.obj X) (F.functor.obj Y)).hom

lemma reducedMap_augmentation : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.reducedMap F X Y ≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedAugmentation V (F.functor.obj X) (F.functor.obj Y) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedAugmentation W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.colimitMap F X Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.reducedMap, ← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_inv, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

lemma graphNormalization_reducedMap (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization W X Y w ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.reducedMap F X Y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap F X Y).app w ≫
        _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization V (F.functor.obj X) (F.functor.obj Y) w := by
  rw [← _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_hom_fac W X Y w]
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.reducedMap]
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.graphInclusion_colimitMap,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso_hom_fac]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative

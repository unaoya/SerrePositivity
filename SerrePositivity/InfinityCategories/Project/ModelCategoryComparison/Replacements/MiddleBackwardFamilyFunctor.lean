module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardFamilyMaps
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagLaws
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ForwardPathZigzagLaws
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendFixedLaws

/-!
# 元の全体の zigzag の関手的な貼り合わせ

概要：元の左右射列と三つの自然な脚の図式を、固定端点の zigzag 図式にする。
方針：元の成分の恒等・合成則を、全ての貼り合わせ頂点で検証する。
規約：添字圏は任意。元の縦弱同値だけを使う。
使われ方：中央の列の置換の関手性と counit/unit の自然性。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFunctor
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {X Y : C} (F : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family D C n m X Y)

lemma zigzagMap_id (d : D) : F.zigzagMap (𝟙 d) = 𝟙 (F.zigzagObj d) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyMaps.zigzagMap
  simp only [F.left.map_id, F.right.map_id, NatTrans.id_app,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ForwardPath.movingHom_id,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingHom_id (W := weakEquivalences C) (X := X)
      (Y := (F.left.obj d).obj 0),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingHom_id (W := weakEquivalences C)
      (X := (F.left.obj d).obj (Fin.last n)) (Y := (F.right.obj d).obj 0),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingHom_id (W := weakEquivalences C)
      (X := (F.right.obj d).obj (Fin.last m)) (Y := Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendLaws.map_id]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
  intro j
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj]
  split_ifs <;> simp

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFunctor (zigzagMap_id)


lemma zigzagMap_comp {d d' d'' : D} (f : d ⟶ d') (g : d' ⟶ d'') :
    F.zigzagMap (f ≫ g) =
      ((F.zigzagMap f : F.zigzagObj d ⟶ F.zigzagObj d') ≫
        (F.zigzagMap g : F.zigzagObj d' ⟶ F.zigzagObj d'') :
          F.zigzagObj d ⟶ F.zigzagObj d'') := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
  intro j
  change (F.zigzagMap (f ≫ g)).app j = (F.zigzagMap f).app j ≫ (F.zigzagMap g).app j
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyMaps.zigzagMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.movingHom,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj]
  split_ifs <;> simp [F.left.map_comp, F.right.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingHom_app_comp_assoc (W := weakEquivalences C), Category.assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFunctor (zigzagMap_comp)


def zigzagFunctor : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y where
  obj := F.zigzagObj
  map := F.zigzagMap
  map_id := F.zigzagMap_id
  map_comp := F.zigzagMap_comp

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFunctor (zigzagFunctor)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFunctor

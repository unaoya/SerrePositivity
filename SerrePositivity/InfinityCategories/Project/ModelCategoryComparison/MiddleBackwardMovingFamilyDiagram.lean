module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyMaps
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagLaws
public import SerrePositivity.EInfinity.Hammock.ForwardPathZigzagLaws
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendFixedLaws

/-!
# 動く局所端点を持つ全体の図式の恒等と合成

概要：元の左右射列と三つの自然な脚の図式を、動く端点の zigzag 図式にする。
方針：元の成分の恒等・合成則を、全ての貼り合わせ頂点で検証する。
規約：添字圏は任意。元の縦弱同値だけを使う。
使われ方：中央の列の置換の関手性と counit/unit の自然性。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyDiagram
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {A B : D ⥤ C} (F : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily D C n m A B)

lemma zigzagMap_id (d : D) : F.zigzagMap (𝟙 d) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id (F.zigzagObj d) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyMaps.zigzagMap, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyMaps.zigzagMapData]
  simp only [F.left.map_id, F.right.map_id, A.map_id, B.map_id, NatTrans.id_app,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison, _root_.SerrePositivity.EInfinity.Hammock.ForwardPath.movingHom_id,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingHom_id (W := weakEquivalences C) (X := A.obj d)
      (Y := (F.left.obj d).obj 0),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingHom_id (W := weakEquivalences C)
      (X := (F.left.obj d).obj (Fin.last n)) (Y := (F.right.obj d).obj 0),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingHom_id (W := weakEquivalences C)
      (X := (F.right.obj d).obj (Fin.last m)) (Y := B.obj d),
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendLaws.map_id]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
  intro j
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj]
  split_ifs <;> simp

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyDiagram (zigzagMap_id)


lemma zigzagMap_comp {d d' d'' : D} (f : d ⟶ d') (g : d' ⟶ d'') :
    F.zigzagMap (f ≫ g) = (F.zigzagMap f).comp (F.zigzagMap g) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
  intro j
  change (F.zigzagMap (f ≫ g)).app j = (F.zigzagMap f).app j ≫ (F.zigzagMap g).app j
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyMaps.zigzagMap, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyMaps.zigzagMapData, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.movingHom,
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily.zigzagObj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj]
  split_ifs <;> simp [F.left.map_comp, F.right.map_comp, A.map_comp, B.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingHom_app_comp_assoc (W := weakEquivalences C), Category.assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyDiagram (zigzagMap_comp)


def movingDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) A B where
  obj := F.zigzagObj
  map := F.zigzagMap
  map_id := F.zigzagMap_id
  map_comp := F.zigzagMap_comp
  first := F.zigzagMap_first
  last := F.zigzagMap_last

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyDiagram (movingDiagram)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyDiagram

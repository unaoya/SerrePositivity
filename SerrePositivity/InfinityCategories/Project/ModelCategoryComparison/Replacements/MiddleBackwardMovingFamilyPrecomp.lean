module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardMovingFamilyReplacementComparisons
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramPrecomp

/-!
# 動く端点を持つブロック図式の前合成

概要：元の左右射列と三つの脚の図式を、同じ元の対象・射に沿って制限する。
方針：端点の評価関手も含めて前合成し、三つの自然変換を whiskerLeft で移す。
規約：全縦弱同値と元の全体の関手を保持する。
使われ方：中央が自明 cofibration の全部分圏上での右置換。
-/

@[expose] public section
universe u v u' v' u'' v''
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPrecomp
open CategoryTheory HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {D' : Type u''} [Category.{v''} D']
  {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {A B : D ⥤ C}
  (F : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily D C n m A B) (K : D' ⥤ D)

def precomp : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily D' C n m (K ⋙ A) (K ⋙ B) where
  left := K ⋙ F.left
  right := K ⋙ F.right
  a := Functor.whiskerLeft K F.a
  middle := Functor.whiskerLeft K F.middle
  b := Functor.whiskerLeft K F.b
  a_mem d := F.a_mem (K.obj d)
  middle_mem d := F.middle_mem (K.obj d)
  b_mem d := F.b_mem (K.obj d)
  left_mem f := F.left_mem (K.map f)
  right_mem f := F.right_mem (K.map f)
  endpoint_left_mem f := F.endpoint_left_mem (K.map f)
  endpoint_right_mem f := F.endpoint_right_mem (K.map f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPrecomp (precomp)


lemma precomp_zigzagObj (d : D') : (F.precomp K).zigzagObj d = F.zigzagObj (K.obj d) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPrecomp (precomp_zigzagObj)


lemma precomp_movingDiagram : (F.precomp K).movingDiagram = F.movingDiagram.precomp K := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPrecomp (precomp_movingDiagram)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPrecomp

module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyReplacementComparisons

/-!
# ブロック図式の前合成

概要：元の左右射列と三つの脚の図式を、同じ元の対象・射に沿って制限する。
方針：二つの関手を前合成し、三つの自然変換を whiskerLeft で移す。
規約：全縦弱同値と元の全体の関手を保持する。
使われ方：中央が自明 cofibration の全部分圏上での右置換。
-/

@[expose] public section
universe u v u' v' u'' v''
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyPrecomp
open CategoryTheory HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {D' : Type u''} [Category.{v''} D']
  {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}
  (F : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family D C n m X Y) (K : D' ⥤ D)

def precomp : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family D' C n m X Y where
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

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyPrecomp (precomp)


lemma precomp_zigzagFunctor : (F.precomp K).zigzagFunctor = K ⋙ F.zigzagFunctor := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyPrecomp (precomp_zigzagFunctor)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyPrecomp

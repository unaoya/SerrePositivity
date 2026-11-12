module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyPushout

/-!
# 元の二つのブロック図式の自然な比較

概要：左右の自然な縦弱同値と三つの脚への整合性を持つ比較を記録する。
方針：元の各対象で左右と中央の正方形を貼り、固定端点の実際の射を得る。
規約：比較の成分は全頂点で弱同値。nerve の弱同値性を仮定しない。
使われ方：動く局所端点を保持する pullback の counit と pushout の unit。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyHom
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {A B : D ⥤ C}

structure Hom (F G : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily D C n m A B) where
  left : F.left ⟶ G.left
  right : F.right ⟶ G.right
  left_mem : ∀ d i, weakEquivalences C ((left.app d).app i)
  right_mem : ∀ d i, weakEquivalences C ((right.app d).app i)
  a_comm : Functor.whiskerRight left (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C n 0) ≫ G.a = F.a
  middle_comm : F.middle ≫ Functor.whiskerRight left (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C n (Fin.last n)) =
    Functor.whiskerRight right (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C m 0) ≫ G.middle
  b_comm : F.b ≫ Functor.whiskerRight right (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pathEvaluation C m (Fin.last m)) = G.b

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyHom (Hom)


namespace Hom
variable {F G : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MovingFamily D C n m A B} (h : Hom F G)

def app (d : D) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom (F.zigzagObj d) (G.zigzagObj d) := by
  let l := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison (h.left.app d) (h.left_mem d)
    (F.a.app d) (G.a.app d) (F.a_mem d) (G.a_mem d)
    (𝟙 (A.obj d)) ((weakEquivalences C).id_mem _)
    ((Category.comp_id _).trans (congr_app h.a_comm d).symm)
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom (F.middle_mem d) (G.middle_mem d)
    ((h.left.app d).app (Fin.last n)) ((h.right.app d).app 0)
    (h.left_mem d _) (h.right_mem d _) (congr_app h.middle_comm d)
  have hj : HEq (l.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n).length)) (c.app 0) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison_last _ _ _ _ _ _ _ _ _
  let lc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map l c hj
  let r := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison (h.right.app d) (h.right_mem d)
    (F.b.app d) (G.b.app d) (F.b_mem d) (G.b_mem d)
    (𝟙 (B.obj d)) ((weakEquivalences C).id_mem _)
    ((congr_app h.b_comm d).trans (Category.id_comp _).symm)
  have hj' : HEq (lc.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)).length)) (r.app 0) := by
    apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq l c hj (Fin.last 1))
    exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison_first _ _ _ _ _ _ _ _ _).symm
  have hf : HEq (lc.app 0) (𝟙 (A.obj d)) := by
    apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq l c 0)
    exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison_first _ _ _ _ _ _ _ _ _
  have hl : HEq (r.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m).length)) (𝟙 (B.obj d)) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison_last _ _ _ _ _ _ _ _ _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedMap lc r hj'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.first_of_heq_id lc hf) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.last_of_heq_id r hl)

end Hom
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingFamilyHom

module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardFamily

/-!
# 元の二つの forward ブロックの図式の全縦射の貼り合わせ

概要：元の左右射列の縦射と三つの自然な脚から、全体の実際の縦弱同値を作る。
方針：左右ブロックと中央の正方形を二度貼り、元の X,Y の固定条件を回収する。
規約：局所端点に恒等射性を要求しない。
使われ方：中央の列の置換の元となる zigzag 図式。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyMaps
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {X Y : C} (F : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family D C n m X Y)

def zigzagMap {d d' : D} (f : d ⟶ d') : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom (F.zigzagObj d) (F.zigzagObj d') := by
  let l := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison (F.left.map f) (F.left_mem f)
    (F.a.app d) (F.a.app d') (F.a_mem d) (F.a_mem d')
    (𝟙 X) ((weakEquivalences C).id_mem _) (F.a.naturality f).symm
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom (F.middle_mem d) (F.middle_mem d')
    ((F.left.map f).app (Fin.last n)) ((F.right.map f).app 0)
    (F.left_mem f _) (F.right_mem f _) (F.middle.naturality f).symm
  have hj : HEq (l.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n).length)) (c.app 0) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison_last _ _ _ _ _ _ _ _ _
  let lc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map l c hj
  let r := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison (F.right.map f) (F.right_mem f)
    (F.b.app d) (F.b.app d') (F.b_mem d) (F.b_mem d')
    (𝟙 Y) ((weakEquivalences C).id_mem _) (F.b.naturality f).symm
  have hj' : HEq (lc.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)).length)) (r.app 0) := by
    apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq l c hj (Fin.last 1))
    exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison_first _ _ _ _ _ _ _ _ _).symm
  have hf : HEq (lc.app 0) (𝟙 X) := by
    apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq l c 0)
    exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison_first _ _ _ _ _ _ _ _ _
  have hl : HEq (r.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m).length)) (𝟙 Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison_last _ _ _ _ _ _ _ _ _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedMap lc r hj'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.first_of_heq_id lc hf) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.last_of_heq_id r hl)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Family export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyMaps (zigzagMap)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyMaps

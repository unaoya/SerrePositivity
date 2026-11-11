module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrow
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPadding

/-!
# 元の三本矢の padding 内の三つの配置

概要：外側・内側・中間の恒等列配置を、同じ元の5列の語の zigzag として作る。
方針：元の二つの弱同値の脚と中間射を保持し、残りの列は恒等射にする。
規約：端点は同じ X と Y、対象語は元の B(threeArrow) そのものである。
使われ方：中間配置からの二つの縦弱同値による比較ホモトピー。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

abbrev word : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.paddingFunctor.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.threeArrow

def outer (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) word X Y where
  vertex := ![X, S.left, S.left, S.right, S.right, Y]
  first := rfl
  last := rfl
  arrow := Fin.cases S.leftMap (Fin.cases (𝟙 S.left)
    (Fin.cases S.middle (Fin.cases (𝟙 S.right) (Fin.cases S.rightMap (fun i => Fin.elim0 i)))))
  backward_mem i hi := by
    change Fin 5 at i
    fin_cases i
    · exact S.left_mem
    · exact (weakEquivalences C).id_mem _
    · cases hi
    · exact (weakEquivalences C).id_mem _
    · exact S.right_mem

def inner (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) word X Y where
  vertex := ![X, X, S.left, S.right, Y, Y]
  first := rfl
  last := rfl
  arrow := Fin.cases (𝟙 X) (Fin.cases S.leftMap
    (Fin.cases S.middle (Fin.cases S.rightMap (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i)))))
  backward_mem i hi := by
    change Fin 5 at i
    fin_cases i
    · exact (weakEquivalences C).id_mem _
    · exact S.left_mem
    · cases hi
    · exact S.right_mem
    · exact (weakEquivalences C).id_mem _

def middle (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) word X Y where
  vertex := ![X, S.left, S.left, S.right, Y, Y]
  first := rfl
  last := rfl
  arrow := Fin.cases S.leftMap (Fin.cases (𝟙 S.left)
    (Fin.cases S.middle (Fin.cases S.rightMap (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i)))))
  backward_mem i hi := by
    change Fin 5 at i
    fin_cases i
    · exact S.left_mem
    · exact (weakEquivalences C).id_mem _
    · cases hi
    · exact S.right_mem
    · exact (weakEquivalences C).id_mem _

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects

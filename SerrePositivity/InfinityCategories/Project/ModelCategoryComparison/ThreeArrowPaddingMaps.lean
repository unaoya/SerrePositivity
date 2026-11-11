module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects

/-!
# 元の三つの padding 配置の関手性

概要：元の三本矢の全縦射は同じ三配置に作用し、恒等と合成を保つ。
方針：元の二つの縦弱同値を繰り返し、恒等射を端点で使う。
規約：全縦射の弱同値性は元の両脚と二つのうち三つから導く。
使われ方：配置間の二つの自然変換。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

def outerMap {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.outer S ⟶ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.outer T where
  app := Fin.cases (𝟙 X) (Fin.cases f.left (Fin.cases f.left
    (Fin.cases f.right (Fin.cases f.right (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i))))))
  app_mem j := by
    change Fin 6 at j
    fin_cases j
    · exact (weakEquivalences C).id_mem _
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.left_weakEquivalence f
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.left_weakEquivalence f
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.right_weakEquivalence f
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.right_weakEquivalence f
    · exact (weakEquivalences C).id_mem _
  first := rfl
  last := rfl
  comm i := by
    change Fin 5 at i
    fin_cases i
    · exact (Category.comp_id _).trans f.left_w.symm
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact f.middle_w
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact f.right_w.trans (Category.id_comp _).symm

def innerMap {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.inner S ⟶ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.inner T where
  app := Fin.cases (𝟙 X) (Fin.cases (𝟙 X) (Fin.cases f.left
    (Fin.cases f.right (Fin.cases (𝟙 Y) (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i))))))
  app_mem j := by
    change Fin 6 at j
    fin_cases j
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.left_weakEquivalence f
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.right_weakEquivalence f
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
  first := rfl
  last := rfl
  comm i := by
    change Fin 5 at i
    fin_cases i
    · rfl
    · exact (Category.comp_id _).trans f.left_w.symm
    · exact f.middle_w
    · exact f.right_w.trans (Category.id_comp _).symm
    · rfl

def middleMap {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.middle S ⟶ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.middle T where
  app := Fin.cases (𝟙 X) (Fin.cases f.left (Fin.cases f.left
    (Fin.cases f.right (Fin.cases (𝟙 Y) (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i))))))
  app_mem j := by
    change Fin 6 at j
    fin_cases j
    · exact (weakEquivalences C).id_mem _
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.left_weakEquivalence f
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.left_weakEquivalence f
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.right_weakEquivalence f
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
  first := rfl
  last := rfl
  comm i := by
    change Fin 5 at i
    fin_cases i
    · exact (Category.comp_id _).trans f.left_w.symm
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact f.middle_w
    · exact f.right_w.trans (Category.id_comp _).symm
    · rfl

def outerFunctor : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.word X Y where
  obj := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.outer
  map := outerMap
  map_id S := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    change Fin 6 at j
    fin_cases j <;> rfl
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    change Fin 6 at j
    fin_cases j <;> first | rfl | exact (Category.id_comp _).symm

def innerFunctor : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.word X Y where
  obj := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.inner
  map := innerMap
  map_id S := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    change Fin 6 at j
    fin_cases j <;> rfl
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    change Fin 6 at j
    fin_cases j <;> first | rfl | exact (Category.id_comp _).symm

def middleFunctor : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.word X Y where
  obj := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowPaddingObjects.middle
  map := middleMap
  map_id S := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    change Fin 6 at j
    fin_cases j <;> rfl
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    change Fin 6 at j
    fin_cases j <;> first | rfl | exact (Category.id_comp _).symm

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison

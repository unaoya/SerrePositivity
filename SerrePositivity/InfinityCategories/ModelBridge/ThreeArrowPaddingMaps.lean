module

public import SerrePositivity.InfinityCategories.ModelBridge.ThreeArrowPaddingObjects

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
namespace SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding
open CategoryTheory HomotopicalAlgebra FrameHom

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X Y : C}

def outerMap {S T : WeakThreeArrow X Y} (f : S ⟶ T) : outer S ⟶ outer T where
  app := Fin.cases (𝟙 X) (Fin.cases f.left (Fin.cases f.left
    (Fin.cases f.right (Fin.cases f.right (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i))))))
  app_mem j := by
    change Fin 6 at j
    fin_cases j
    · exact (weakEquivalences C).id_mem _
    · exact WeakThreeArrow.left_weakEquivalence f
    · exact WeakThreeArrow.left_weakEquivalence f
    · exact WeakThreeArrow.right_weakEquivalence f
    · exact WeakThreeArrow.right_weakEquivalence f
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

def innerMap {S T : WeakThreeArrow X Y} (f : S ⟶ T) : inner S ⟶ inner T where
  app := Fin.cases (𝟙 X) (Fin.cases (𝟙 X) (Fin.cases f.left
    (Fin.cases f.right (Fin.cases (𝟙 Y) (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i))))))
  app_mem j := by
    change Fin 6 at j
    fin_cases j
    · exact (weakEquivalences C).id_mem _
    · exact (weakEquivalences C).id_mem _
    · exact WeakThreeArrow.left_weakEquivalence f
    · exact WeakThreeArrow.right_weakEquivalence f
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

def middleMap {S T : WeakThreeArrow X Y} (f : S ⟶ T) : middle S ⟶ middle T where
  app := Fin.cases (𝟙 X) (Fin.cases f.left (Fin.cases f.left
    (Fin.cases f.right (Fin.cases (𝟙 Y) (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i))))))
  app_mem j := by
    change Fin 6 at j
    fin_cases j
    · exact (weakEquivalences C).id_mem _
    · exact WeakThreeArrow.left_weakEquivalence f
    · exact WeakThreeArrow.left_weakEquivalence f
    · exact WeakThreeArrow.right_weakEquivalence f
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

def outerFunctor : WeakThreeArrow X Y ⥤ Zigzag (weakEquivalences C) word X Y where
  obj := outer
  map := outerMap
  map_id S := by
    apply Zigzag.hom_ext
    intro j
    change Fin 6 at j
    fin_cases j <;> rfl
  map_comp f g := by
    apply Zigzag.hom_ext
    intro j
    change Fin 6 at j
    fin_cases j <;> first | rfl | exact (Category.id_comp _).symm

def innerFunctor : WeakThreeArrow X Y ⥤ Zigzag (weakEquivalences C) word X Y where
  obj := inner
  map := innerMap
  map_id S := by
    apply Zigzag.hom_ext
    intro j
    change Fin 6 at j
    fin_cases j <;> rfl
  map_comp f g := by
    apply Zigzag.hom_ext
    intro j
    change Fin 6 at j
    fin_cases j <;> first | rfl | exact (Category.id_comp _).symm

def middleFunctor : WeakThreeArrow X Y ⥤ Zigzag (weakEquivalences C) word X Y where
  obj := middle
  map := middleMap
  map_id S := by
    apply Zigzag.hom_ext
    intro j
    change Fin 6 at j
    fin_cases j <;> rfl
  map_comp f g := by
    apply Zigzag.hom_ext
    intro j
    change Fin 6 at j
    fin_cases j <;> first | rfl | exact (Category.id_comp _).symm

end SerrePositivity.EInfinity.Hammock.ThreeArrow.Padding

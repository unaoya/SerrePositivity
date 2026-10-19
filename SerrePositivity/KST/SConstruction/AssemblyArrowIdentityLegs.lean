module
public import SerrePositivity.KST.SConstruction.AssemblyInputArrows

/-! # 恒等入力射から指定入力射への二つの脚
概要：入力射 f:X→Y を恒等入力射 id_X と id_Y に結ぶ cospan を作る。
方針：源側は後合成 f、標的側は前合成 f を使う。
規約：両側合成の向きを固定し、元の入力射を変更しない。
使われ方：over 圏の coherent な全選択から元の自然性の二脚を回収する。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 源の恒等入力射から、指定射への後合成の脚。 -/
def assemblyArrowFromSource {I : Type v} [Category.{w} I] {X Y : I} (f : X ⟶ Y) :
    assemblyArrowMk (𝟙 X) ⟶ assemblyArrowMk f := assemblyArrowMap (𝟙 X) f (by
    change (𝟙 X) ≫ (𝟙 X) ≫ f = f
    simp)

/-- 標的の恒等入力射から、指定射への前合成の脚。 -/
def assemblyArrowFromTarget {I : Type v} [Category.{w} I] {X Y : I} (f : X ⟶ Y) :
    assemblyArrowMk (𝟙 Y) ⟶ assemblyArrowMk f := assemblyArrowMap f (𝟙 Y) (by
    change f ≫ (𝟙 Y) ≫ (𝟙 Y) = f
    simp)

/-- 源側の脚の前合成は恒等射。 -/
lemma assemblyArrowFromSource_pre {I : Type v} [Category.{w} I] {X Y : I} (f : X ⟶ Y) :
    assemblyArrowPre (assemblyArrowFromSource f) = 𝟙 X := rfl

/-- 源側の脚の後合成は指定射。 -/
lemma assemblyArrowFromSource_post {I : Type v} [Category.{w} I] {X Y : I} (f : X ⟶ Y) :
    assemblyArrowPost (assemblyArrowFromSource f) = f := rfl

/-- 標的側の脚の前合成は指定射。 -/
lemma assemblyArrowFromTarget_pre {I : Type v} [Category.{w} I] {X Y : I} (f : X ⟶ Y) :
    assemblyArrowPre (assemblyArrowFromTarget f) = f := rfl

/-- 標的側の脚の後合成は恒等射。 -/
lemma assemblyArrowFromTarget_post {I : Type v} [Category.{w} I] {X Y : I} (f : X ⟶ Y) :
    assemblyArrowPost (assemblyArrowFromTarget f) = 𝟙 Y := rfl

end SerrePositivity.KST.SConstruction

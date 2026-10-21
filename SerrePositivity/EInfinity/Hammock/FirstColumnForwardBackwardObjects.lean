module

public import SerrePositivity.EInfinity.Hammock.CoefficientProduct
public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardForwardObjects
public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardBackwardObjects
public import SerrePositivity.EInfinity.Hammock.ZigzagAppendRightBoundaryHom

/-!
# 先頭 forward・backward の元の係数と切断

概要：元の接合点と全縦射を持つ混合二方向の分解。
方針：通常 Hom と残りの backward 語を同じ共変係数の積にする。
規約：元の指定射・全対象・全射を保持する。
使われ方：DK9.4・10.3の全語の帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : Word) (X Y : C)
abbrev forwardBackwardSource := Zigzag W (Word.append (Word.single .forward)
  (Word.cons .backward w)) X Y
def forwardBackwardRightCoefficient : WideSubcategory W ⥤ Cat.{u, u} :=
  CoefficientProduct.diagram (forwardRightCoefficient W X) (backwardRightCoefficient W w Y)
abbrev forwardBackwardTarget := TwoSidedGrothendieck.total
  CoefficientProduct.point (forwardBackwardRightCoefficient W w X Y)
def forwardBackwardObject (S : forwardBackwardSource W w X Y) : forwardBackwardTarget W w X Y :=
  TwoSidedGrothendieck.mk _ _ ⟨ZigzagAppend.Part.jointFunctor.obj S⟩
    (Discrete.mk PUnit.unit)
    (Discrete.mk (ForwardZigzag.value (ZigzagAppend.Part.leftObj S)), ZigzagAppend.Part.rightObj S)
def forwardBackwardBase {S T : forwardBackwardSource W w X Y} (h : S ⟶ T) :
    TwoSidedGrothendieck.base _ _ (forwardBackwardObject W w X Y S) ⟶
      TwoSidedGrothendieck.base _ _ (forwardBackwardObject W w X Y T) :=
  ⟨ZigzagAppend.Part.jointFunctor.map h, h.app_mem _⟩
lemma forwardBackwardHead_comm {S T : forwardBackwardSource W w X Y} (h : S ⟶ T) :
    ForwardZigzag.value (ZigzagAppend.Part.leftObj S) ≫ (forwardBackwardBase W w X Y h).hom =
      ForwardZigzag.value (ZigzagAppend.Part.leftObj T) := by
  have hc := ForwardZigzag.value_moving (ZigzagAppend.Part.leftMap h) h.first
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hc
  convert hc using 1 <;> rfl
def forwardBackwardMap {S T : forwardBackwardSource W w X Y} (h : S ⟶ T) :
    forwardBackwardObject W w X Y S ⟶ forwardBackwardObject W w X Y T :=
  TwoSidedGrothendieck.homMk (forwardBackwardBase W w X Y h)
    (𝟙 (Discrete.mk PUnit.unit))
    ⟨eqToHom (Discrete.ext (forwardBackwardHead_comm W w X Y h)),
      backwardMovingToHom (forwardBackwardBase W w X Y h).property
        (ZigzagAppend.Part.rightBoundaryHom h)⟩
end SerrePositivity.EInfinity.Hammock.FirstColumn

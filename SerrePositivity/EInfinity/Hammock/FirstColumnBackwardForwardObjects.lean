module

public import SerrePositivity.EInfinity.Hammock.CoefficientProduct
public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardForwardObjects
public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardBackwardObjects
public import SerrePositivity.EInfinity.Hammock.ZigzagAppendRightBoundaryHom

/-!
# 先頭 backward・forward の元の係数と切断

概要：元の指定 Hom と残りの語を同じ反変係数の積へ回収する。
方針：元の接合点・全縦成分と貼り戻しの全往復を使う。
規約：元の切断関手自体を保持する。
使われ方：DK9.4・10.3の残る混合二方向の分解。
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
abbrev backwardForwardSource := Zigzag W (Word.append (Word.single .backward)
  (Word.cons .forward w)) X Y
def backwardForwardLeftCoefficient : (WideSubcategory W)ᵒᵖ ⥤ Cat.{u, u} :=
  CoefficientProduct.diagram (backwardLeftCoefficient W X) (forwardLeftCoefficient W w Y)
abbrev backwardForwardTarget := TwoSidedGrothendieck.total
  (backwardForwardLeftCoefficient W w X Y) CoefficientProduct.point
def backwardForwardObject (S : backwardForwardSource W w X Y) : backwardForwardTarget W w X Y :=
  TwoSidedGrothendieck.mk _ _ ⟨ZigzagAppend.Part.jointFunctor.obj S⟩
    (Discrete.mk (BackwardZigzag.markedHomEquiv
      (BackwardZigzag.value (ZigzagAppend.Part.leftObj S))), ZigzagAppend.Part.rightObj S)
    (Discrete.mk PUnit.unit)
def backwardForwardBase {S T : backwardForwardSource W w X Y} (h : S ⟶ T) :
    TwoSidedGrothendieck.base _ _ (backwardForwardObject W w X Y S) ⟶
      TwoSidedGrothendieck.base _ _ (backwardForwardObject W w X Y T) :=
  ⟨ZigzagAppend.Part.jointFunctor.map h, h.app_mem _⟩
lemma backwardForwardHead_comm {S T : backwardForwardSource W w X Y} (h : S ⟶ T) :
    BackwardZigzag.markedHomEquiv (BackwardZigzag.value (ZigzagAppend.Part.leftObj S)) =
      backwardForwardBase W w X Y h ≫
        BackwardZigzag.markedHomEquiv (BackwardZigzag.value (ZigzagAppend.Part.leftObj T)) := by
  apply WideSubcategory.hom_ext
  have hc := BackwardZigzag.value_moving (ZigzagAppend.Part.leftMap h) h.first
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hc
  convert hc using 1 <;> rfl
def backwardForwardMap {S T : backwardForwardSource W w X Y} (h : S ⟶ T) :
    backwardForwardObject W w X Y S ⟶ backwardForwardObject W w X Y T :=
  TwoSidedGrothendieck.homMk (backwardForwardBase W w X Y h)
    ⟨eqToHom (Discrete.ext (backwardForwardHead_comm W w X Y h)),
      forwardMovingToHom (ZigzagAppend.Part.rightBoundaryHom h)⟩
    (𝟙 (Discrete.mk PUnit.unit))
end SerrePositivity.EInfinity.Hammock.FirstColumn

module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendRightBoundaryHom
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagBackwardMovingEquiv
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagFirstBoundaryBackwardLaws
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.BackwardZigzagNativeDiscrete
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SingleZigzagMovingValue
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.TwoSidedGrothendieckHomComponents
public import Mathlib.CategoryTheory.Yoneda

/-!
# 元の後向き二列の接合点と両係数

概要：元の接合点の指定射と両側の全縦成分を保持して切断する。
方針：指定 Hom の反変係数と残りの語の共変係数を使う。
規約：元の指定部分圏と実際の全射を使う。
使われ方：DK9.4・10.3の後向き二列の分解。
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
def backwardLeftCoefficient : (WideSubcategory W)ᵒᵖ ⥤ Cat.{u, u} :=
  yoneda.obj (⟨X⟩ : WideSubcategory W) ⋙ typeToCat
def backwardRightCoefficient : WideSubcategory W ⥤ Cat.{u, u} :=
  backwardCovariant w Y
abbrev backwardBackwardSource := Zigzag W (Word.append (Word.single .backward)
  (Word.cons .backward w)) X Y
abbrev backwardBackwardTarget := TwoSidedGrothendieck.total
  (backwardLeftCoefficient W X) (backwardRightCoefficient W w Y)
def backwardBackwardObject (S : backwardBackwardSource W w X Y) :
    backwardBackwardTarget W w X Y :=
  TwoSidedGrothendieck.mk _ _ ⟨ZigzagAppend.Part.jointFunctor.obj S⟩
    (Discrete.mk (BackwardZigzag.markedHomEquiv
      (BackwardZigzag.value (ZigzagAppend.Part.leftObj S))))
    (ZigzagAppend.Part.rightObj S)
def backwardBackwardBase {S T : backwardBackwardSource W w X Y} (h : S ⟶ T) :
    TwoSidedGrothendieck.base _ _ (backwardBackwardObject W w X Y S) ⟶
      TwoSidedGrothendieck.base _ _ (backwardBackwardObject W w X Y T) :=
  ⟨ZigzagAppend.Part.jointFunctor.map h, h.app_mem _⟩
def backwardBackwardBoundary {S T : backwardBackwardSource W w X Y} (h : S ⟶ T) :
    BoundaryHom (backwardBackwardBase W w X Y h).hom
      (ZigzagAppend.Part.rightObj S) (ZigzagAppend.Part.rightObj T) :=
  ZigzagAppend.Part.rightBoundaryHom h
lemma backwardBackwardHead_comm {S T : backwardBackwardSource W w X Y} (h : S ⟶ T) :
    BackwardZigzag.markedHomEquiv (BackwardZigzag.value (ZigzagAppend.Part.leftObj S)) =
      backwardBackwardBase W w X Y h ≫
        BackwardZigzag.markedHomEquiv (BackwardZigzag.value (ZigzagAppend.Part.leftObj T)) := by
  apply WideSubcategory.hom_ext
  have hc := BackwardZigzag.value_moving (ZigzagAppend.Part.leftMap h) h.first
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hc
  convert hc using 1 <;> rfl

def backwardBackwardMap {S T : backwardBackwardSource W w X Y} (h : S ⟶ T) :
    backwardBackwardObject W w X Y S ⟶ backwardBackwardObject W w X Y T :=
  TwoSidedGrothendieck.homMk (backwardBackwardBase W w X Y h)
    (eqToHom (Discrete.ext (backwardBackwardHead_comm W w X Y h)))
    (backwardMovingToHom (backwardBackwardBase W w X Y h).property
      (backwardBackwardBoundary W w X Y h))
end SerrePositivity.EInfinity.Hammock.FirstColumn

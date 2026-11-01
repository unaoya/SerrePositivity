module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagForwardMovingEquiv
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendPartDiagrams
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SingleZigzagMovingValue
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagFirstBoundaryForwardLaws
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.TwoSidedGrothendieckHomComponents
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# 元の二つの forward 列の切断と三成分

概要：先頭の一列と残りの元の語を接合点で切り出す。
方針：底の指定射・残りの全縦射・先頭列の Hom を保持する。
規約：元の対象と全縦射を使う。圏同値と他の向きは後続。
使われ方：DK9.4・10.3の全語の分解。
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
def forwardLeftCoefficient : (WideSubcategory W)ᵒᵖ ⥤ Cat.{u, u} :=
  (wideSubcategoryInclusion W).op ⋙ forwardContravariant (W := W) w Y
def forwardRightCoefficient : WideSubcategory W ⥤ Cat.{u, u} :=
  wideSubcategoryInclusion W ⋙ coyoneda.obj (op X) ⋙ typeToCat
abbrev forwardForwardSource := Zigzag W (Word.append (Word.single .forward)
  (Word.cons .forward w)) X Y
abbrev forwardForwardTarget := TwoSidedGrothendieck.total
  (forwardLeftCoefficient W w Y) (forwardRightCoefficient W X)
def forwardForwardObject (S : forwardForwardSource W w X Y) : forwardForwardTarget W w X Y :=
  TwoSidedGrothendieck.mk _ _ ⟨(ZigzagAppend.Part.jointFunctor.obj S)⟩
    (ZigzagAppend.Part.rightObj S) (Discrete.mk (ForwardZigzag.value (ZigzagAppend.Part.leftObj S)))

def forwardForwardBase {S T : forwardForwardSource W w X Y} (h : S ⟶ T) :
    (TwoSidedGrothendieck.base _ _ (forwardForwardObject W w X Y S)) ⟶
      (TwoSidedGrothendieck.base _ _ (forwardForwardObject W w X Y T)) :=
  ⟨(ZigzagAppend.Part.jointFunctor.map h), h.app_mem _⟩

def forwardForwardBoundary {S T : forwardForwardSource W w X Y} (h : S ⟶ T) :
    BoundaryHom (forwardForwardBase W w X Y h).hom
      (ZigzagAppend.Part.rightObj S) (ZigzagAppend.Part.rightObj T) where
  hom := ZigzagAppend.Part.rightMap h
  first := (conj_eqToHom_iff_heq _ _ (ZigzagAppend.Part.rightObj S).first
    (ZigzagAppend.Part.rightObj T).first).mpr
    ((ZigzagAppend.Part.rightDiagram (a := Word.single .forward)).first h)
  last := (ZigzagAppend.Part.rightMap h).last_of_heq_id
    ((ZigzagAppend.Part.rightDiagram (a := Word.single .forward)).last h)

lemma forwardForwardHead_comm {S T : forwardForwardSource W w X Y} (h : S ⟶ T) :
    ForwardZigzag.value (ZigzagAppend.Part.leftObj S) ≫ (forwardForwardBase W w X Y h).hom =
      ForwardZigzag.value (ZigzagAppend.Part.leftObj T) := by
  have hc := ForwardZigzag.value_moving (ZigzagAppend.Part.leftMap h) h.first
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hc
  convert hc using 1 <;> rfl

def forwardForwardMap {S T : forwardForwardSource W w X Y} (h : S ⟶ T) :
    forwardForwardObject W w X Y S ⟶ forwardForwardObject W w X Y T :=
  TwoSidedGrothendieck.homMk (forwardForwardBase W w X Y h)
    (forwardMovingToHom (forwardForwardBoundary W w X Y h))
    (eqToHom (Discrete.ext (forwardForwardHead_comm W w X Y h)))

end SerrePositivity.EInfinity.Hammock.FirstColumn

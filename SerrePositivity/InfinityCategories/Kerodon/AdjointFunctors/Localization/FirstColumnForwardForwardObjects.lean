module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagForwardMovingEquiv
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SingleZigzagMovingValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryForwardLaws
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# 元の二つの forward 列の切断と三成分

概要：先頭の一列と残りの元の語を接合点で切り出す。
方針：底の指定射・残りの全縦射・先頭列の Hom を保持する。
規約：元の対象と全縦射を使う。圏同値と他の向きは後続。
使われ方：DK9.4・10.3の全語の分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)
def forwardLeftCoefficient : (WideSubcategory W)ᵒᵖ ⥤ Cat.{u, u} :=
  (wideSubcategoryInclusion W).op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardContravariant (W := W) w Y
def forwardRightCoefficient : WideSubcategory W ⥤ Cat.{u, u} :=
  wideSubcategoryInclusion W ⋙ coyoneda.obj (op X) ⋙ typeToCat
abbrev forwardForwardSource := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w)) X Y
abbrev forwardForwardTarget := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total
  (forwardLeftCoefficient W w Y) (forwardRightCoefficient W X)
def forwardForwardObject (S : forwardForwardSource W w X Y) : forwardForwardTarget W w X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.mk _ _ ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.jointFunctor.obj S)⟩
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S) (Discrete.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S)))

def forwardForwardBase {S T : forwardForwardSource W w X Y} (h : S ⟶ T) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ (forwardForwardObject W w X Y S)) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ (forwardForwardObject W w X Y T)) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.jointFunctor.map h), h.app_mem _⟩

def forwardForwardBoundary {S T : forwardForwardSource W w X Y} (h : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom (forwardForwardBase W w X Y h).hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj T) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartMaps.rightMap h
  first := (conj_eqToHom_iff_heq _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S).first
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj T).first).mpr
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.rightDiagram (a := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)).first h)
  last := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartMaps.rightMap h).last_of_heq_id
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.rightDiagram (a := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)).last h)

lemma forwardForwardHead_comm {S T : forwardForwardSource W w X Y} (h : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S) ≫ (forwardForwardBase W w X Y h).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj T) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.value_moving (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartMaps.leftMap h) h.first
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hc
  convert hc using 1 <;> rfl

def forwardForwardMap {S T : forwardForwardSource W w X Y} (h : S ⟶ T) :
    forwardForwardObject W w X Y S ⟶ forwardForwardObject W w X Y T :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk (forwardForwardBase W w X Y h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardMovingToHom (forwardForwardBoundary W w X Y h))
    (eqToHom (Discrete.ext (forwardForwardHead_comm W w X Y h)))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

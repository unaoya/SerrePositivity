module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardForwardObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnBackwardBackwardObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendRightBoundaryHom

/-!
# 先頭 forward・backward の元の係数と切断

概要：元の接合点と全縦射を持つ混合二方向の分解。
方針：通常 Hom と残りの backward 語を同じ共変係数の積にする。
規約：元の指定射・全対象・全射を保持する。
使われ方：DK9.4・10.3の全語の帰納。

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
abbrev forwardBackwardSource := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)) X Y
def forwardBackwardRightCoefficient : WideSubcategory W ⥤ Cat.{u, u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardRightCoefficient W X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardRightCoefficient W w Y)
abbrev forwardBackwardTarget := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.point (forwardBackwardRightCoefficient W w X Y)
def forwardBackwardObject (S : forwardBackwardSource W w X Y) : forwardBackwardTarget W w X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.mk _ _ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.jointFunctor.obj S⟩
    (Discrete.mk PUnit.unit)
    (Discrete.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S)), _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S)
def forwardBackwardBase {S T : forwardBackwardSource W w X Y} (h : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ (forwardBackwardObject W w X Y S) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ (forwardBackwardObject W w X Y T) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.jointFunctor.map h, h.app_mem _⟩
lemma forwardBackwardHead_comm {S T : forwardBackwardSource W w X Y} (h : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S) ≫ (forwardBackwardBase W w X Y h).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj T) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.value_moving (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartMaps.leftMap h) h.first
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hc
  convert hc using 1 <;> rfl
def forwardBackwardMap {S T : forwardBackwardSource W w X Y} (h : S ⟶ T) :
    forwardBackwardObject W w X Y S ⟶ forwardBackwardObject W w X Y T :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk (forwardBackwardBase W w X Y h)
    (𝟙 (Discrete.mk PUnit.unit))
    ⟨eqToHom (Discrete.ext (forwardBackwardHead_comm W w X Y h)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardMovingToHom (forwardBackwardBase W w X Y h).property
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightBoundaryHom h)⟩
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

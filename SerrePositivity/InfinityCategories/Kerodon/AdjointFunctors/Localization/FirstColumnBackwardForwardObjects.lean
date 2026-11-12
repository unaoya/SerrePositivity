module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardForwardObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnBackwardBackwardObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendRightBoundaryHom

/-!
# 先頭 backward・forward の元の係数と切断

概要：元の指定 Hom と残りの語を同じ反変係数の積へ回収する。
方針：元の接合点・全縦成分と貼り戻しの全往復を使う。
規約：元の切断関手自体を保持する。
使われ方：DK9.4・10.3の残る混合二方向の分解。

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
abbrev backwardForwardSource := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w)) X Y
def backwardForwardLeftCoefficient : (WideSubcategory W)ᵒᵖ ⥤ Cat.{u, u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.diagram (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardLeftCoefficient W X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardLeftCoefficient W w Y)
abbrev backwardForwardTarget := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total
  (backwardForwardLeftCoefficient W w X Y) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.CoefficientProduct.point
def backwardForwardObject (S : backwardForwardSource W w X Y) : backwardForwardTarget W w X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.mk _ _ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.jointFunctor.obj S⟩
    (Discrete.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S))), _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S)
    (Discrete.mk PUnit.unit)
def backwardForwardBase {S T : backwardForwardSource W w X Y} (h : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ (backwardForwardObject W w X Y S) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ (backwardForwardObject W w X Y T) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.jointFunctor.map h, h.app_mem _⟩
lemma backwardForwardHead_comm {S T : backwardForwardSource W w X Y} (h : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S)) =
      backwardForwardBase W w X Y h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj T)) := by
  apply WideSubcategory.hom_ext
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.value_moving (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartMaps.leftMap h) h.first
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hc
  convert hc using 1 <;> rfl
def backwardForwardMap {S T : backwardForwardSource W w X Y} (h : S ⟶ T) :
    backwardForwardObject W w X Y S ⟶ backwardForwardObject W w X Y T :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk (backwardForwardBase W w X Y h)
    ⟨eqToHom (Discrete.ext (backwardForwardHead_comm W w X Y h)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardMovingToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightBoundaryHom h)⟩
    (𝟙 (Discrete.mk PUnit.unit))
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendRightBoundaryHom
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagBackwardMovingEquiv
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardLaws
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagNativeDiscrete
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SingleZigzagMovingValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents
public import Mathlib.CategoryTheory.Yoneda

/-!
# 元の後向き二列の接合点と両係数

概要：元の接合点の指定射と両側の全縦成分を保持して切断する。
方針：指定 Hom の反変係数と残りの語の共変係数を使う。
規約：元の指定部分圏と実際の全射を使う。
使われ方：DK9.4・10.3の後向き二列の分解。

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
def backwardLeftCoefficient : (WideSubcategory W)ᵒᵖ ⥤ Cat.{u, u} :=
  yoneda.obj (⟨X⟩ : WideSubcategory W) ⋙ typeToCat
def backwardRightCoefficient : WideSubcategory W ⥤ Cat.{u, u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardCovariant w Y
abbrev backwardBackwardSource := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)) X Y
abbrev backwardBackwardTarget := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total
  (backwardLeftCoefficient W X) (backwardRightCoefficient W w Y)
def backwardBackwardObject (S : backwardBackwardSource W w X Y) :
    backwardBackwardTarget W w X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.mk _ _ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.jointFunctor.obj S⟩
    (Discrete.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S)
def backwardBackwardBase {S T : backwardBackwardSource W w X Y} (h : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ (backwardBackwardObject W w X Y S) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.base _ _ (backwardBackwardObject W w X Y T) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartDiagrams.jointFunctor.map h, h.app_mem _⟩
def backwardBackwardBoundary {S T : backwardBackwardSource W w X Y} (h : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom (backwardBackwardBase W w X Y h).hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj T) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightBoundaryHom h
lemma backwardBackwardHead_comm {S T : backwardBackwardSource W w X Y} (h : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S)) =
      backwardBackwardBase W w X Y h ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj T)) := by
  apply WideSubcategory.hom_ext
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.value_moving (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendPartMaps.leftMap h) h.first
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hc
  convert hc using 1 <;> rfl

def backwardBackwardMap {S T : backwardBackwardSource W w X Y} (h : S ⟶ T) :
    backwardBackwardObject W w X Y S ⟶ backwardBackwardObject W w X Y T :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk (backwardBackwardBase W w X Y h)
    (eqToHom (Discrete.ext (backwardBackwardHead_comm W w X Y h)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardMovingToHom (backwardBackwardBase W w X Y h).property
      (backwardBackwardBoundary W w X Y h))
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingWordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramWordChange
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramExt

/-!
# 動く全図式の元の語の作用の単位・合成・表示変更

概要：元の WordAction の法則を全図式の厳密な等式として回収する。
方針：全対象は元の法則、全縦射は同じ cut の成分で照合する。
規約：固定端点性を仮定しない。
使われ方：元の括弧を持つ refinedDiagram の圧縮。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B : D ⥤ C}

lemma wordAction_id (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction (𝟙 a) F = F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ext
  · intro d
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.obj_id (F.obj d)
  · intro d e f j
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq (F.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.cut_id a j)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (wordAction_id)


lemma wordAction_comp (f : a ⟶ b) (g : b ⟶ c) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction (f ≫ g) F = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction f F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ext
  · intro d
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordComposition.obj_comp f g (F.obj d)
  · intro d e h j
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.app_heq (F.map h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.cut_comp f g j)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (wordAction_comp)


lemma wordAction_eqToHom (h : a = b) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction (eqToHom h) F = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord h F := by
  cases h
  exact wordAction_id F

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (wordAction_eqToHom)


lemma changeWord_heq (h : a = b) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord h F) F := by cases h; rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (changeWord_heq)


lemma changeWord_eq_of_heq (h : a = b) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B)
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b A B) (hFG : HEq F G) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord h F = G :=
  eq_of_heq ((changeWord_heq h F).trans hFG)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (changeWord_eq_of_heq)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

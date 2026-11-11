module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramPrecomp

/-!
# 固定端点の回収と指定部分圏への持ち上げの表示変更

概要：全図式の異種等式を固定端点の関手と指定部分圏の関手へ移す。
方針：語と端点の表示で帰納し、元の全射を保持する。
規約：所属証明の選択には依存しない。
使われ方：実際の W-hammock 単体の単体作用素への整合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD uI vI
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' Y Y' : C}

lemma fixedFunctor_heq (hw : a = b) (hX : X = X') (hY : Y = Y')
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a ((Functor.const D).obj X) ((Functor.const D).obj Y))
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b ((Functor.const D).obj X') ((Functor.const D).obj Y'))
    (hFG : HEq F G) : HEq F.fixedFunctor G.fixedFunctor := by
  cases hw
  cases hX
  cases hY
  have he := eq_of_heq hFG
  cases he
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (fixedFunctor_heq)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {I : Type uI} [Category.{vI} I]
  {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' Y Y' : C}

lemma liftFunctor_heq (hw : a = b) (hX : X = X') (hY : Y = Y')
    (F : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (G : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b X' Y')
    (hF : ∀ d j, W ((F.obj d).arrow j)) (hG : ∀ d j, W ((G.obj d).arrow j))
    (hFG : HEq F G) : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.liftFunctor W F hF) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.liftFunctor W G hG) := by
  cases hw
  cases hX
  cases hY
  have he := eq_of_heq hFG
  cases he
  rfl

lemma liftFunctor_precomp {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C} (K : I ⥤ D)
    (F : D ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (hF : ∀ d j, W ((F.obj d).arrow j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.liftFunctor W (K ⋙ F) (fun d j => hF (K.obj d) j) = K ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedZigzagLift.liftFunctor W F hF := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

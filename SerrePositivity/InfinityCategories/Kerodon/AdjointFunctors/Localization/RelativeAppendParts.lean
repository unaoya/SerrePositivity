module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeAppendObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendParts

/-!
# 元の相対関手による前後の部分の回収

概要：元の相対関手と全ての端点表示を保って切断の各成分を送る。
方針：元の指定部分圏の関手と全係数の元の自然変換を使う。
規約：始点・終点の表示を等式で移し、元の射を保持する。
使われ方：DK9.4・10.3の分解の全相対作用素への自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C} {X' Y' : D} (F : LocalizerMorphism W V)
  (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
lemma left_relative_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX rfl).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftObj S) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j; rfl
  · intro i
    change HEq (eqToHom _ ≫ F.functor.map (S.arrow (i.castAdd b.length)) ≫ eqToHom _)
      (F.functor.map (eqToHom _ ≫ S.arrow (i.castAdd b.length) ≫ eqToHom _))
    simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    rfl
lemma right_relative_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F rfl hY).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightObj S) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j; rfl
  · intro i
    change HEq (eqToHom _ ≫ F.functor.map (S.arrow (i.natAdd a.length)) ≫ eqToHom _)
      (F.functor.map (eqToHom _ ≫ S.arrow (i.natAdd a.length) ≫ eqToHom _))
    simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    rfl
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

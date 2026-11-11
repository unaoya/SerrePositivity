module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardLaws
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor
/-!
# 元の始点の指定射の後合成と相対関手の厳密な整合

概要：先頭 backward の元の後合成は、相対関手の同じ全対象・全縦射への作用に自然。
方針：元の先頭の合成と残りの全列の端点移送を関手で送り、同じ射列へ戻す。
規約：指定射の保存と固定した終点の表示の等式も保持する。
使われ方：DK10.3の元の語の共変 transfunctor の単体作用素。

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
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' Y : C} {Y' : D} (F : LocalizerMorphism W V) (hY : F.functor.obj Y = Y')

lemma backward_relative_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y)
    (f : X ⟶ X') (hf : W f) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F rfl hY).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward S f hf) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F rfl hY).obj S) (F.functor.map f) (F.map f hf) := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ ?_ ?_
  · intro j
    cases j using Fin.cases <;> rfl
  · intro i
    cases i using Fin.cases with
    | zero =>
      change HEq (F.functor.map (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ f))
        (F.functor.map (S.arrow (0 : Fin (w.length + 1))) ≫
          eqToHom (congrArg F.functor.obj S.first) ≫ F.functor.map f)
      simp only [Functor.map_comp, eqToHom_map]
      rfl
    | succ i =>
      change HEq (F.functor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow S X' i))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F rfl hY).obj S) (F.functor.obj X') i)
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow
      simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
        heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
      rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backward_relative_obj export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backward_relative_obj)


lemma backward_relative_functor (f : X ⟶ X') (hf : W f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps.backwardFunctor (W := W) (w := w) (Y := Y) f hf ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F rfl hY =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F rfl hY ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps.backwardFunctor (F.functor.map f) (F.map f hf) := by
  refine CategoryTheory.Functor.hext (fun S => backward_relative_obj F hY S f hf) ?_
  intro S T h
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (backward_relative_obj F hY S f hf)
    (backward_relative_obj F hY T f hf) _ _ ?_
  intro j
  cases j using Fin.cases with
  | zero => exact heq_of_eq (F.functor.map_id X')
  | succ j => rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backward_relative_functor export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backward_relative_functor)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

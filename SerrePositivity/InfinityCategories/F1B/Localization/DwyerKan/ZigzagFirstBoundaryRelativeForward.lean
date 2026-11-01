module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagFirstBoundaryForwardLaws
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeFixedZigzagFunctor
/-!
# 元の始点の前合成と相対関手の厳密な整合

概要：先頭 forward の境界の元の前合成は、相対関手の同じ全対象・全縦射への作用に自然。
方針：元の先頭の合成と残りの全列の端点移送を関手で送り、同じ射列に戻す。
規約：固定した終点の表示の等式も保持する。
使われ方：DK10.3の元の語の反変 transfunctor の単体作用素。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
open CategoryTheory
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {w : Word} {X X' Y : C} {Y' : D} (F : LocalizerMorphism W V) (hY : F.functor.obj Y = Y')

lemma forward_relative_obj (S : Zigzag W (Word.cons .forward w) X Y) (f : X' ⟶ X) :
    (Relative.fixedFunctor F rfl hY).obj (forward S f) =
      forward ((Relative.fixedFunctor F rfl hY).obj S) (F.functor.map f) := by
  refine Zigzag.object_ext _ _ ?_ ?_
  · intro j
    cases j using Fin.cases <;> rfl
  · intro i
    cases i using Fin.cases with
    | zero =>
      change HEq (F.functor.map (f ≫ eqToHom S.first.symm ≫ S.arrow (0 : Fin (w.length + 1))))
        (F.functor.map f ≫ eqToHom (congrArg F.functor.obj S.first.symm) ≫
          F.functor.map (S.arrow (0 : Fin (w.length + 1))))
      simp only [Functor.map_comp, eqToHom_map]
      rfl
    | succ i =>
      change HEq (F.functor.map (tailArrow S X' i))
        (tailArrow ((Relative.fixedFunctor F rfl hY).obj S) (F.functor.obj X') i)
      unfold tailArrow
      simp only [Functor.map_comp, eqToHom_map, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
        heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
      rfl

lemma forward_relative_functor (f : X' ⟶ X) :
    forwardFunctor (W := W) (w := w) (Y := Y) f ⋙ Relative.fixedFunctor F rfl hY =
      Relative.fixedFunctor F rfl hY ⋙ forwardFunctor (F.functor.map f) := by
  refine CategoryTheory.Functor.hext (fun S => forward_relative_obj F hY S f) ?_
  intro S T h
  refine Zigzag.hom_hext (forward_relative_obj F hY S f) (forward_relative_obj F hY T f) _ _ ?_
  intro j
  cases j using Fin.cases with
  | zero => exact heq_of_eq (F.functor.map_id X')
  | succ j => rfl
end SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary

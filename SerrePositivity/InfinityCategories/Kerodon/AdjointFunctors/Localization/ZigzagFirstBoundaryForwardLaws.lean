module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomFixed
/-!
# 元の始点の前合成の恒等・合成と反変係数関手

概要：先頭 forward の語の始点を動かす元の操作は恒等と合成に厳密に両立する。
方針：元の全頂点・全列と全縦成分を端点移送込みで照合する。
規約：元の zigzag の圏から C の反対圏上の Cat 値関手を構成する。
使われ方：DK9.3・10.3の元の語の始点に関する反変性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory Opposite
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' X'' Y : C}

omit [W.IsMultiplicative] in
lemma forward_id_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward S (𝟙 X) = S := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ ?_ ?_
  · intro j
    cases j using Fin.cases with
    | zero => exact S.first.symm
    | succ j => rfl
  · intro i
    cases i using Fin.cases with
    | zero =>
      change HEq ((𝟙 X) ≫ eqToHom S.first.symm ≫ S.arrow (0 : Fin (w.length + 1)))
        (S.arrow (0 : Fin (w.length + 1)))
      simp only [Category.id_comp, eqToHom_comp_heq_iff]
      rfl
    | succ i =>
      change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow S X i) (S.arrow i.succ)
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow
      simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
      rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward_id_obj export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forward_id_obj)


omit [W.IsMultiplicative] in
lemma forward_comp_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X Y)
    (f : X' ⟶ X) (g : X'' ⟶ X') : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward S f) g = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward S (g ≫ f) := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ (fun _ => rfl) ?_
  intro i
  cases i using Fin.cases with
  | zero =>
    apply heq_of_eq
    change g ≫ (𝟙 X') ≫ f ≫ eqToHom S.first.symm ≫ S.arrow (0 : Fin (w.length + 1)) =
      (g ≫ f) ≫ eqToHom S.first.symm ≫ S.arrow (0 : Fin (w.length + 1))
    simp only [Category.id_comp, Category.assoc]
  | succ i =>
    change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward S f) X'' i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow S X'' i)
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow S X' i) (S.arrow i.succ)
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward_comp_obj export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forward_comp_obj)


lemma forwardFunctor_id : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.forwardFunctor (W := W) (w := w) (Y := Y) (𝟙 X) = 𝟭 _ := by
  refine CategoryTheory.Functor.hext forward_id_obj ?_
  intro S T h
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (forward_id_obj S) (forward_id_obj T) _ _ ?_
  intro j
  cases j using Fin.cases with
  | zero => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofHom_first h).symm
  | succ j => rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardFunctor_id export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardFunctor_id)


lemma forwardFunctor_comp (f : X' ⟶ X) (g : X'' ⟶ X') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.forwardFunctor (W := W) (w := w) (Y := Y) f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.forwardFunctor g = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.forwardFunctor (g ≫ f) := by
  refine CategoryTheory.Functor.hext (fun S => forward_comp_obj S f g) ?_
  intro S T h
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (forward_comp_obj S f g) (forward_comp_obj T f g) _ _ ?_
  intro j
  cases j using Fin.cases <;> rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardFunctor_comp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardFunctor_comp)


def forwardContravariant (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (Y : C) : Cᵒᵖ ⥤ Cat.{u, u} where
  obj X := Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X.unop Y)
  map f := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.forwardFunctor f.unop).toCatHom
  map_id X := by apply Cat.Hom.ext; exact forwardFunctor_id
  map_comp f g := by apply Cat.Hom.ext; exact (forwardFunctor_comp f.unop g.unop).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardContravariant export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardContravariant)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

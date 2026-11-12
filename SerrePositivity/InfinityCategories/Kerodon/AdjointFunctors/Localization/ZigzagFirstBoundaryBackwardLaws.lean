module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomFixed
public import Mathlib.CategoryTheory.Widesubcategory
/-!
# 元の始点の後合成の恒等・合成と共変係数関手

概要：先頭 backward の語の始点を指定射で動かす元の操作を共変関手にする。
方針：元の全頂点・全列と全縦成分の恒等・合成を端点移送込みで照合する。
規約：指定部分圏の元の全射と弱同値の指定条件を保持する。
使われ方：DK9.3・10.3の元の語の始点に関する共変性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' X'' Y : C}

lemma backward_id_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward S (𝟙 X) (W.id_mem X) = S := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ ?_ ?_
  · intro j
    cases j using Fin.cases with
    | zero => exact S.first.symm
    | succ j => rfl
  · intro i
    cases i using Fin.cases with
    | zero =>
      change HEq (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ (𝟙 X))
        (S.arrow (0 : Fin (w.length + 1)))
      simp only [Category.comp_id, comp_eqToHom_heq_iff]
      rfl
    | succ i =>
      change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow S X i) (S.arrow i.succ)
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow
      simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
      rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backward_id_obj export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backward_id_obj)


lemma backward_comp_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y)
    (f : X ⟶ X') (hf : W f) (g : X' ⟶ X'') (hg : W g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward S f hf) g hg = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward S (f ≫ g) (W.comp_mem _ _ hf hg) := by
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ (fun _ => rfl) ?_
  intro i
  cases i using Fin.cases with
  | zero =>
    apply heq_of_eq
    change (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ f) ≫ (𝟙 X') ≫ g =
      S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ (f ≫ g)
    simp only [Category.id_comp, Category.assoc]
  | succ i =>
    change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward S f hf) X'' i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow S X'' i)
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow S X' i) (S.arrow i.succ)
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backward_comp_obj export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backward_comp_obj)


lemma backwardFunctor_id : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps.backwardFunctor (W := W) (w := w) (Y := Y) (𝟙 X) (W.id_mem X) =
    𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y) := by
  refine CategoryTheory.Functor.hext backward_id_obj ?_
  intro S T h
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (backward_id_obj S) (backward_id_obj T) _ _ ?_
  intro j
  cases j using Fin.cases with
  | zero => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofHom_first h).symm
  | succ j => rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardFunctor_id export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardFunctor_id)


lemma backwardFunctor_comp (f : X ⟶ X') (hf : W f) (g : X' ⟶ X'') (hg : W g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps.backwardFunctor (W := W) (w := w) (Y := Y) f hf ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps.backwardFunctor g hg =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps.backwardFunctor (f ≫ g) (W.comp_mem _ _ hf hg) := by
  refine CategoryTheory.Functor.hext (fun S => backward_comp_obj S f hf g hg) ?_
  intro S T h
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (backward_comp_obj S f hf g hg) (backward_comp_obj T f hf g hg) _ _ ?_
  intro j
  cases j using Fin.cases <;> rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardFunctor_comp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardFunctor_comp)


def backwardCovariant (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (Y : C) : WideSubcategory W ⥤ Cat.{u, u} where
  obj X := Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X.obj Y)
  map f := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps.backwardFunctor f.hom f.property).toCatHom
  map_id X := by apply Cat.Hom.ext; exact backwardFunctor_id
  map_comp f g := by
    apply Cat.Hom.ext
    exact (backwardFunctor_comp f.hom f.property g.hom g.property).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardCovariant export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardCovariant)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

module

public import SerrePositivity.EInfinity.Hammock.ZigzagFirstBoundaryBackwardMaps
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingHomFixed
public import Mathlib.CategoryTheory.Widesubcategory
/-!
# 元の始点の後合成の恒等・合成と共変係数関手

概要：先頭 backward の語の始点を指定射で動かす元の操作を共変関手にする。
方針：元の全頂点・全列と全縦成分の恒等・合成を端点移送込みで照合する。
規約：指定部分圏の元の全射と弱同値の指定条件を保持する。
使われ方：DK9.3・10.3の元の語の始点に関する共変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : Word} {X X' X'' Y : C}

lemma backward_id_obj (S : Zigzag W (Word.cons .backward w) X Y) :
    backward S (𝟙 X) (W.id_mem X) = S := by
  refine Zigzag.object_ext _ _ ?_ ?_
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
      change HEq (tailArrow S X i) (S.arrow i.succ)
      unfold tailArrow
      simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
      rfl

lemma backward_comp_obj (S : Zigzag W (Word.cons .backward w) X Y)
    (f : X ⟶ X') (hf : W f) (g : X' ⟶ X'') (hg : W g) :
    backward (backward S f hf) g hg = backward S (f ≫ g) (W.comp_mem _ _ hf hg) := by
  refine Zigzag.object_ext _ _ (fun _ => rfl) ?_
  intro i
  cases i using Fin.cases with
  | zero =>
    apply heq_of_eq
    change (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ f) ≫ (𝟙 X') ≫ g =
      S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ (f ≫ g)
    simp only [Category.id_comp, Category.assoc]
  | succ i =>
    change HEq (tailArrow (backward S f hf) X'' i) (tailArrow S X'' i)
    unfold tailArrow
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    change HEq (tailArrow S X' i) (S.arrow i.succ)
    unfold tailArrow
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl

lemma backwardFunctor_id : backwardFunctor (W := W) (w := w) (Y := Y) (𝟙 X) (W.id_mem X) =
    𝟭 (Zigzag W (Word.cons .backward w) X Y) := by
  refine CategoryTheory.Functor.hext backward_id_obj ?_
  intro S T h
  refine Zigzag.hom_hext (backward_id_obj S) (backward_id_obj T) _ _ ?_
  intro j
  cases j using Fin.cases with
  | zero => exact (MovingHom.ofHom_first h).symm
  | succ j => rfl

lemma backwardFunctor_comp (f : X ⟶ X') (hf : W f) (g : X' ⟶ X'') (hg : W g) :
    backwardFunctor (W := W) (w := w) (Y := Y) f hf ⋙ backwardFunctor g hg =
      backwardFunctor (f ≫ g) (W.comp_mem _ _ hf hg) := by
  refine CategoryTheory.Functor.hext (fun S => backward_comp_obj S f hf g hg) ?_
  intro S T h
  refine Zigzag.hom_hext (backward_comp_obj S f hf g hg) (backward_comp_obj T f hf g hg) _ _ ?_
  intro j
  cases j using Fin.cases <;> rfl

def backwardCovariant (w : Word) (Y : C) : WideSubcategory W ⥤ Cat.{u, u} where
  obj X := Cat.of (Zigzag W (Word.cons .backward w) X.obj Y)
  map f := (backwardFunctor f.hom f.property).toCatHom
  map_id X := by apply Cat.Hom.ext; exact backwardFunctor_id
  map_comp f g := by
    apply Cat.Hom.ext
    exact (backwardFunctor_comp f.hom f.property g.hom g.property).symm
end SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary

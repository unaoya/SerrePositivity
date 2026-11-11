module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagPathIntervalValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnRecovery

/-!
# 元の語の作用と値の射列の切断の両立

概要：圧縮した語の各列の値は、元の値の射列の対応区間の射に等しい。
方針：元の fiber の方向付き合成を回収し、元の切断関手で射列を制限する。
規約：空 fiber の恒等列も元の写像の一部として扱う。
使われ方：元の WordAction による値の不変性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] (L : C ⥤ D) (hL : W.IsInvertedBy L)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

lemma wordAction_edge (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (j : Fin b.length) (hj : b.direction j = d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intervalValue L hL d S (f.cut j.castSucc) (f.cut j.succ)
        (f.cut_monotone (Fin.castSucc_le_succ j))
        (fun i hi hi' => (f.fiber_direction j i hi hi').trans hj) := by
  cases d with
  | forward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j hj]
    exact congrArg L.map (eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq f S .forward j hj))
  | backward =>
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j hj]
    have hh : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j hj =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.intervalBackwardIso L hL S (f.cut j.castSucc) (f.cut j.succ)
          (f.cut_monotone (Fin.castSucc_le_succ j))
          (fun i hi hi' => (f.fiber_direction j i hi hi').trans hj) := by
      apply Iso.ext
      change L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j hj).unop =
        L.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S _ _ _ _).unop
      exact congrArg L.map
        (congrArg Quiver.Hom.unop (eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrow_obj_heq f S .backward j hj)))
    exact congrArg Iso.inv hh

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.wordAction_edge export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (wordAction_edge)


def cutFunctor (f : a ⟶ b) : Fin (b.length + 1) ⥤ Fin (a.length + 1) :=
  (⟨f.cut, f.cut_monotone⟩ : Fin (b.length + 1) →o Fin (a.length + 1)).toFunctor

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.cutFunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (cutFunctor)


lemma path_wordAction (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) = cutFunctor f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S := by
  apply ComposableArrows.ext (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S))
    (G := cutFunctor f ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S) (fun _ => rfl)
  intro i hi
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S)).map (homOfLE (Fin.castSucc_le_succ ⟨i, hi⟩)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S).map (homOfLE (f.cut_monotone (Fin.castSucc_le_succ ⟨i, hi⟩)))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_map_adjacent L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) ⟨i, hi⟩).trans
    ((wordAction_edge L hL f S _ ⟨i, hi⟩ rfl).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_interval L hL _ S _ _ _ _).symm)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.path_wordAction export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (path_wordAction)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

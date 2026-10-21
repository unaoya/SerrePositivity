module

public import SerrePositivity.EInfinity.Hammock.ZigzagPathIntervalValue
public import SerrePositivity.EInfinity.Hammock.WordColumnRecovery

/-!
# 元の語の作用と値の射列の切断の両立

概要：圧縮した語の各列の値は、元の値の射列の対応区間の射に等しい。
方針：元の fiber の方向付き合成を回収し、元の切断関手で射列を制限する。
規約：空 fiber の恒等列も元の写像の一部として扱う。
使われ方：元の WordAction による値の不変性。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Value
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] (L : C ⥤ D) (hL : W.IsInvertedBy L)
  {a b : Word} {X Y : C}

lemma wordAction_edge (f : a ⟶ b) (S : Zigzag W a X Y) (d : Direction)
    (j : Fin b.length) (hj : b.direction j = d) :
    edge L hL (WordAction.obj f S) j =
      intervalValue L hL d S (f.cut j.castSucc) (f.cut j.succ)
        (f.cut_monotone (Fin.castSucc_le_succ j))
        (fun i hi hi' => (f.fiber_direction j i hi hi').trans hj) := by
  cases d with
  | forward =>
    rw [edge_forward L hL (WordAction.obj f S) j hj]
    exact congrArg L.map (eq_of_heq (WordAction.arrow_obj_heq f S .forward j hj))
  | backward =>
    rw [edge_backward L hL (WordAction.obj f S) j hj]
    have hh : backwardIso L hL (WordAction.obj f S) j hj =
        intervalBackwardIso L hL S (f.cut j.castSucc) (f.cut j.succ)
          (f.cut_monotone (Fin.castSucc_le_succ j))
          (fun i hi hi' => (f.fiber_direction j i hi hi').trans hj) := by
      apply Iso.ext
      change L.map (Direction.arrow .backward (WordAction.obj f S) j hj).unop =
        L.map (Segment.map .backward S _ _ _ _).unop
      exact congrArg L.map
        (congrArg Quiver.Hom.unop (eq_of_heq (WordAction.arrow_obj_heq f S .backward j hj)))
    exact congrArg Iso.inv hh

def cutFunctor (f : a ⟶ b) : Fin (b.length + 1) ⥤ Fin (a.length + 1) :=
  (⟨f.cut, f.cut_monotone⟩ : Fin (b.length + 1) →o Fin (a.length + 1)).toFunctor

lemma path_wordAction (f : a ⟶ b) (S : Zigzag W a X Y) :
    path L hL (WordAction.obj f S) = cutFunctor f ⋙ path L hL S := by
  apply ComposableArrows.ext (F := path L hL (WordAction.obj f S))
    (G := cutFunctor f ⋙ path L hL S) (fun _ => rfl)
  intro i hi
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (path L hL (WordAction.obj f S)).map (homOfLE (Fin.castSucc_le_succ ⟨i, hi⟩)) =
    (path L hL S).map (homOfLE (f.cut_monotone (Fin.castSucc_le_succ ⟨i, hi⟩)))
  exact (path_map_adjacent L hL (WordAction.obj f S) ⟨i, hi⟩).trans
    ((wordAction_edge L hL f S _ ⟨i, hi⟩ rfl).trans (path_interval L hL _ S _ _ _ _).symm)

end SerrePositivity.EInfinity.Hammock.Zigzag.Value

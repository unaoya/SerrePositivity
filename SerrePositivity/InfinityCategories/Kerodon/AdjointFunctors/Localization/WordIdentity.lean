module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentAdjacent
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt

/-!
# 恒等語による元の恒等遷移関手

概要：語の恒等写像による遷移は、元の zigzag 圏の恒等関手に厳密に一致する。
方針：切断位置の恒等性と一列の区間合成の回収を全対象・全縦射で使う。
規約：端点の移送を含め、元の関手の等式として証明する。
使われ方：語で添字付ける hammock 図式の単位則。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

/-- 区間の両端の等式は、元の区間合成の異種等式を与える。 -/
lemma segment_heq_of_eq (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y)
    {p q p' q' : Fin (w.length + 1)} (hp : p = p') (hq : q = q')
    (hpq : p ≤ q) (hpq' : p' ≤ q')
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = d)
    (hd' : ∀ i : Fin w.length, p'.val ≤ i.val → i.val < q'.val → w.direction i = d) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S p q hpq hd) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S p' q' hpq' hd') := by
  cases hp
  cases hq
  rfl

/-- 全頂点の同定と向きに応じた射の同定は、元の列の異種等式を与える。 -/
lemma columnAux_heq {I : Type*} (V U : I → C) (hV : V = U) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : I)
    (m : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (V p) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (V q))
    (n : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (U p) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (U q)) (hm : HEq m n) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.columnAux V d p q m) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.columnAux U d p q n) := by
  cases hV
  have h := eq_of_heq hm
  cases h
  rfl

/-- 元の列の向きを移して戻すと、同じ元の列を回収する。 -/
lemma columnAux_arrow_heq (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length)
    (hi : w.direction i = d) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.columnAux S.vertex d i.castSucc i.succ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d S i hi)) (S.arrow i) := by
  cases d
  · change HEq (eqToHom _ ≫ S.arrow i ≫ eqToHom _) (S.arrow i)
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl
  · change HEq (eqToHom _ ≫ S.arrow i ≫ eqToHom _) (S.arrow i)
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl

/-- 恒等語による圧縮の全列は、元の同じ列。 -/
lemma column_id_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column (𝟙 w) S i) (S.arrow i) := by
  let V := fun j => S.vertex ((𝟙 w : w ⟶ w).cut j)
  have hV : V = S.vertex := funext (fun j => congrArg S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.cut_id w j))
  have h := segment_heq_of_eq (w.direction i) S
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.cut_id w i.castSucc) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.cut_id w i.succ)
    ((𝟙 w : w ⟶ w).cut_monotone (Fin.castSucc_le_succ i)) (Fin.castSucc_le_succ i)
    (fun j hj hj' => (𝟙 w : w ⟶ w).fiber_direction i j hj hj')
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.adjacent_direction _ i rfl)
  have hm := h.trans (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_adjacent (w.direction i) S i rfl))
  exact (columnAux_heq V S.vertex hV _ _ _ _ _ hm).trans
    (columnAux_arrow_heq (w.direction i) S i rfl)

/-- 恒等語による全対象の像は、元の同じ zigzag。 -/
lemma obj_id [W.IsMultiplicative] (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (𝟙 w) S = S :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ (fun j => congrArg S.vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.cut_id w j)) (column_id_heq S)

/-- 恒等語による遷移は、元の全対象・全縦射の恒等関手。 -/
lemma functor_id [W.IsMultiplicative] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor (W := W) (X := X) (Y := Y) (𝟙 w) = 𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) := by
  apply Functor.hext (fun S => obj_id S)
  intro S T g
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (obj_id S) (obj_id T)
  intro j
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.app_heq g (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom.cut_id w j)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordIdentity

/-!
# 圧縮した一列から元の fiber 合成の回収

概要：圧縮した列をその向きの圏へ移すと、元の fiber の合成を回収する。
方針：向きの変換を相殺し、端点の等式だけの移送を異種等式で取り除く。
規約：元の列の向きと切断位置を保持する。
使われ方：二つの語の写像に沿う圧縮と一度の圧縮の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

lemma columnAux_forward_heq {I : Type*} (V : I → C) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : I)
    (m : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (V p) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (V q)) (hd : d = .forward) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.columnAux V d p q m) m := by
  subst d
  rfl

lemma columnAux_backward_heq {I : Type*} (V : I → C) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : I)
    (m : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (V p) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (V q)) (hd : d = .backward) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.columnAux V d p q m).op m := by
  subst d
  rfl

lemma segment_direction_heq (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (d d' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (hdd : d = d')
    (p q : Fin (a.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d)
    (hd' : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d') :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S p q hpq hd) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d' S p q hpq hd') := by
  cases hdd
  rfl

/-- 圧縮した列の同じ向きの射は、元の fiber の合成と異種等しい。 -/
lemma arrow_obj_heq [W.IsMultiplicative] (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (j : Fin b.length) (hj : b.direction j = d) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) j hj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S (f.cut j.castSucc) (f.cut j.succ)
        (f.cut_monotone (Fin.castSucc_le_succ j))
        (fun i hi hi' => (f.fiber_direction j i hi hi').trans hj)) := by
  cases d
  · change HEq (eqToHom _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column f S j ≫ eqToHom _) _
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact (columnAux_forward_heq _ _ _ _ _ hj).trans
      (segment_direction_heq S _ _ hj _ _ _ _ _)
  · change HEq (eqToHom _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column f S j ≫ eqToHom _).op _
    simp only [op_comp, eqToHom_op, Category.assoc,
      eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact (columnAux_backward_heq _ _ _ _ _ hj).trans
      (segment_direction_heq S _ _ hj _ _ _ _ _)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

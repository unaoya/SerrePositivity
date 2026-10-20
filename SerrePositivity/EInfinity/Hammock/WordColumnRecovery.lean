module

public import SerrePositivity.EInfinity.Hammock.WordIdentity

/-!
# 圧縮した一列から元の fiber 合成の回収

概要：圧縮した列をその向きの圏へ移すと、元の fiber の合成を回収する。
方針：向きの変換を相殺し、端点の等式だけの移送を異種等式で取り除く。
規約：元の列の向きと切断位置を保持する。
使われ方：二つの語の写像に沿う圧縮と一度の圧縮の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.WordAction
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : Word} {X Y : C}

lemma columnAux_forward_heq {I : Type*} (V : I → C) (d : Direction) (p q : I)
    (m : Direction.vertex d (V p) ⟶ Direction.vertex d (V q)) (hd : d = .forward) :
    HEq (columnAux V d p q m) m := by
  subst d
  rfl

lemma columnAux_backward_heq {I : Type*} (V : I → C) (d : Direction) (p q : I)
    (m : Direction.vertex d (V p) ⟶ Direction.vertex d (V q)) (hd : d = .backward) :
    HEq (columnAux V d p q m).op m := by
  subst d
  rfl

lemma segment_direction_heq (S : Zigzag W a X Y) (d d' : Direction) (hdd : d = d')
    (p q : Fin (a.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d)
    (hd' : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d') :
    HEq (Segment.map d S p q hpq hd) (Segment.map d' S p q hpq hd') := by
  cases hdd
  rfl

/-- 圧縮した列の同じ向きの射は、元の fiber の合成と異種等しい。 -/
lemma arrow_obj_heq [W.IsMultiplicative] (f : a ⟶ b) (S : Zigzag W a X Y)
    (d : Direction) (j : Fin b.length) (hj : b.direction j = d) :
    HEq (Direction.arrow d (obj f S) j hj)
      (Segment.map d S (f.cut j.castSucc) (f.cut j.succ)
        (f.cut_monotone (Fin.castSucc_le_succ j))
        (fun i hi hi' => (f.fiber_direction j i hi hi').trans hj)) := by
  cases d
  · change HEq (eqToHom _ ≫ column f S j ≫ eqToHom _) _
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact (columnAux_forward_heq _ _ _ _ _ hj).trans
      (segment_direction_heq S _ _ hj _ _ _ _ _)
  · change HEq (eqToHom _ ≫ column f S j ≫ eqToHom _).op _
    simp only [op_comp, eqToHom_op, Category.assoc,
      eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact (columnAux_backward_heq _ _ _ _ _ hj).trans
      (segment_direction_heq S _ _ hj _ _ _ _ _)

end SerrePositivity.EInfinity.Hammock.WordAction

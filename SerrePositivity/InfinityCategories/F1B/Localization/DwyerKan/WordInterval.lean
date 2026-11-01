module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordColumnRecovery

/-!
# 語の写像に沿う区間の切断と向き

概要：終域の同方向区間に対応する元の連続区間の向きと頂点を照合する。
方針：初期区間の切断の特徴付けから列の像の上下界を導く。
規約：空 fiber を含む非狭義の単調写像を使う。
使われ方：圧縮後の区間合成を元の区間の合成と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.WordAction
open CategoryTheory

variable {a b : Word}

/-- 終域の同方向区間の元の切断間の全列も、同じ方向。 -/
lemma interval_direction (f : a ⟶ b) (d : Direction) (p q : Fin (b.length + 1))
    (hd : ∀ j : Fin b.length, p.val ≤ j.val → j.val < q.val → b.direction j = d)
    (i : Fin a.length) (hi : (f.cut p).val ≤ i.val) (hi' : i.val < (f.cut q).val) :
    a.direction i = d := by
  have h₀ := f.lt_cut_iff p i
  have h₁ := f.lt_cut_iff q i
  have hleft : p.val ≤ (f.orderHom i).val := by omega
  have hright : (f.orderHom i).val < q.val := h₁.1 hi'
  exact (f.direction_eq i).symm.trans (hd (f.orderHom i) hleft hright)

lemma interval_index_ge (p q : Fin (b.length + 1)) (hpq : p ≤ q)
    (k : Fin (q.val - p.val + 1)) : p ≤ Segment.index p q hpq k := by
  change p.val ≤ p.val + k.val
  omega

lemma interval_index_le (p q : Fin (b.length + 1)) (hpq : p ≤ q)
    (k : Fin (q.val - p.val + 1)) : Segment.index p q hpq k ≤ q := by
  change p.val + k.val ≤ q.val
  have := k.isLt
  omega

/-- 終域の区間の各頂点を、元の切断間の区間内の位置へ送る。 -/
def intervalPosition (f : a ⟶ b) (p q : Fin (b.length + 1)) (hpq : p ≤ q) :
    Fin (q.val - p.val + 1) →o Fin ((f.cut q).val - (f.cut p).val + 1) where
  toFun k := Segment.coordinate (f.cut p) (f.cut q) (f.cut (Segment.index p q hpq k))
    (f.cut_monotone (interval_index_ge p q hpq k))
    (f.cut_monotone (interval_index_le p q hpq k))
  monotone' i j hij := by
    have hidx : Segment.index p q hpq i ≤ Segment.index p q hpq j :=
      Nat.add_le_add_left hij _
    exact Nat.sub_le_sub_right (f.cut_monotone hidx) _

lemma index_intervalPosition (f : a ⟶ b) (p q : Fin (b.length + 1)) (hpq : p ≤ q)
    (k : Fin (q.val - p.val + 1)) :
    Segment.index (f.cut p) (f.cut q) (f.cut_monotone hpq) (intervalPosition f p q hpq k) =
      f.cut (Segment.index p q hpq k) :=
  Segment.index_coordinate _ _ _
    (f.cut_monotone (interval_index_ge p q hpq k))
    (f.cut_monotone (interval_index_le p q hpq k))

@[simp] lemma intervalPosition_zero (f : a ⟶ b) (p q : Fin (b.length + 1)) (hpq : p ≤ q) :
    intervalPosition f p q hpq 0 = 0 := by
  apply Fin.ext
  dsimp [intervalPosition, Segment.coordinate]
  rw [Segment.index_zero]
  exact Nat.sub_self _

@[simp] lemma intervalPosition_last (f : a ⟶ b) (p q : Fin (b.length + 1)) (hpq : p ≤ q) :
    intervalPosition f p q hpq (Fin.last (q.val - p.val)) =
      Fin.last ((f.cut q).val - (f.cut p).val) := by
  apply Fin.ext
  dsimp [intervalPosition, Segment.coordinate]
  rw [Segment.index_last]

end SerrePositivity.EInfinity.Hammock.WordAction

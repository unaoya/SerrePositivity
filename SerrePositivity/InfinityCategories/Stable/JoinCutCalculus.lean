module
public import SerrePositivity.InfinityCategories.Stable.JoinReassociation

/-! # 二段の join の切断の引き戻し

概要：先頭区間の中の切断と、後半区間の切断の引き戻しを元の区間の切断で計算する。
方針：切断の頂点による特徴づけと自然数の加減算を使う。
規約：空区間を含む任意の有限順序集合。
使われ方：S4 の join の結合同型の自然性。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：切断の引き戻しは切断位置に関して単調。
方針：先頭区間の逆像を有限集合の包含として比較する。
規約：切断が終域の頂点数を超える場合も含む。
使われ方：二段の切断の引き戻しの上界。 -/
lemma stablePullCut_mono {m n : ℕ} (α : Fin m →o Fin n) {a b : ℕ} (h : a ≤ b) :
    Join.pullCut α a ≤ Join.pullCut α b := by
  unfold Join.pullCut
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  omega

/-- 概要：左区間の中の切断の引き戻しは元の順序写像による引き戻しに等しい。
方針：各頂点で両方の切断の左側に入る条件を比較する。
規約：内側の切断 a は外側の切断 b 以下。
使われ方：三因子の第一因子の頂点数の自然性。 -/
lemma stablePullCut_leftMap {m n : ℕ} (α : Fin m →o Fin n) {a b : ℕ} (hab : a ≤ b) :
    Join.pullCut (Join.leftMap α b) a = Join.pullCut α a := by
  apply Join.cut_ext ((Join.pullCut_le _ _).trans (Join.pullCut_le α b))
    (Join.pullCut_le α a)
  intro i
  constructor
  · intro hi
    have hib : i.val < Join.pullCut α b := lt_of_lt_of_le hi (Join.pullCut_le _ _)
    have hα := (Join.lt_pullCut_iff (Join.leftMap α b) a ⟨i.val, hib⟩).mp hi
    apply (Join.lt_pullCut_iff α a i).mpr
    exact hα
  · intro hi
    have hib : i.val < Join.pullCut α b := lt_of_lt_of_le hi (stablePullCut_mono α hab)
    have hα := (Join.lt_pullCut_iff α a i).mp hi
    exact (Join.lt_pullCut_iff (Join.leftMap α b) a ⟨i.val, hib⟩).mpr hα

/-- 概要：右区間の中の切断の引き戻しは二つの元の切断の差に等しい。
方針：後半区間の頂点を元の区間へ戻し、値と添字の原点移動を計算する。
規約：a と b はそれぞれ前半と右区間内の頂点数。
使われ方：三因子の第二因子の頂点数の自然性。 -/
lemma stablePullCut_rightMap {m n : ℕ} (α : Fin m →o Fin n) (a b : ℕ) :
    Join.pullCut (Join.rightMap α a) b = Join.pullCut α (a + b) - Join.pullCut α a := by
  have hab : Join.pullCut α a ≤ Join.pullCut α (a + b) := stablePullCut_mono α (by omega)
  have hm := Join.pullCut_le α (a + b)
  apply Join.cut_ext (Join.pullCut_le _ _) (by omega :
    Join.pullCut α (a + b) - Join.pullCut α a ≤ m - Join.pullCut α a)
  intro i
  let j : Fin m := ⟨Join.pullCut α a + i.val, by have := i.isLt; omega⟩
  have hα : a ≤ (α j).val := by
    by_contra h
    have hj := (Join.lt_pullCut_iff α a j).mpr (Nat.lt_of_not_ge h)
    dsimp only [j] at hj
    omega
  have he : (Join.rightMap α a i).val = (α j).val - a := rfl
  rw [Join.lt_pullCut_iff, he]
  have hj := Join.lt_pullCut_iff α (a + b) j
  dsimp only [j] at hj hα ⊢
  omega

/-- 概要：元の二つの切断の間の区間の引き戻しの頂点数は切断の引き戻しの差。
方針：右区間の公式で b-a を使い、a+(b-a)=b を代入する。
規約：a≤b。使われ方：三因子の第二因子の自然性。 -/
lemma stablePullCut_middle {m n : ℕ} (α : Fin m →o Fin n) {a b : ℕ} (hab : a ≤ b) :
    Join.pullCut (Join.rightMap α a) (b - a) = Join.pullCut α b - Join.pullCut α a := by
  simpa only [Nat.add_sub_of_le hab] using stablePullCut_rightMap α a (b - a)

end SerrePositivity.InfinityCategories

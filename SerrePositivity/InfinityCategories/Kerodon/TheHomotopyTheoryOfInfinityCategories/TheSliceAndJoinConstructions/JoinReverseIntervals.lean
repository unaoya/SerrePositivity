module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReverseCuts

/-! # 反転による join の左右区間の交換

概要：反転した順序写像の左・右への制限を、元の写像の右・左への制限の反転で計算する。
方針：切断の補数の公式と、区間の添字の反転を使う。
規約：写像の値を自然数として比較する。使われ方：join の反転の自然性。

対応節は Kerodon 4.3（Tag 015M）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：反転した写像の右区間は元の左区間を反転したもの。
方針：右区間の原点移動を切断の補数で置き換え、二つの元の頂点が同じことを示す。
規約：i と j は同じ自然数値を持つ。使われ方：反転後の第一因子の自然性。 -/
lemma stableReverseRightMap_val {m n : ℕ} (α : Fin m →o Fin n) (a : ℕ) (ha : a ≤ n)
    (i : Fin (m - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom α) a))
    (j : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (n - a))) (hij : i.val = j.val) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom α) a i).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α (n - a)) j).val := by
  let u : Fin m := (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom α) a + i.val, by
    have := i.isLt; omega⟩ : Fin m).rev
  let v : Fin m := ⟨j.rev.val, lt_of_lt_of_le j.rev.isLt (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α (n - a))⟩
  have huv : u = v := by
    apply Fin.ext
    dsimp only [u, v]
    simp only [Fin.val_rev]
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stablePullCut_reverse α a ha
    have hbound := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α (n - a)
    have hi := i.isLt
    have hj := j.isLt
    omega
  change (α u).rev.val - a = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α (n - a) j.rev).rev.val
  simp only [Fin.val_rev]
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α (n - a) j.rev).val = (α v).val := rfl
  rw [hv, huv]
  have hα := (α v).isLt
  omega

/-- 概要：反転した写像の左区間は元の右区間を反転したもの。
方針：右区間の反転した添字を元の区間に戻し、値が切断以上であることを使う。
規約：a は終域の頂点数以下。使われ方：反転後の第二因子の自然性。 -/
lemma stableReverseLeftMap_val {m n : ℕ} (α : Fin m →o Fin n) (a : ℕ) (_ha : a ≤ n)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom α) a))
    (j : Fin (m - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (n - a))) (hij : i.val = j.val) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom α) a i).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α (n - a)) j).val := by
  let u : Fin m := (⟨i.val, lt_of_lt_of_le i.isLt
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableReverseOrderHom α) a)⟩ : Fin m).rev
  let v : Fin m := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (n - a) + j.rev.val, by have := j.rev.isLt; omega⟩
  have huv : u = v := by
    apply Fin.ext
    dsimp only [u, v]
    simp only [Fin.val_rev]
    have hj := j.isLt
    omega
  have hα : n - a ≤ (α v).val := by
    by_contra h
    have hv := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff α (n - a) v).mpr (Nat.lt_of_not_ge h)
    dsimp only [v] at hv
    omega
  change (α u).rev.val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α (n - a) j.rev).rev.val
  simp only [Fin.val_rev]
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α (n - a) j.rev).val = (α v).val - (n - a) := rfl
  rw [hv, huv]
  have hαn := (α v).isLt
  omega

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

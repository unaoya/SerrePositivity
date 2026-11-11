module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinReassociationNaturality
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.Data.Fin.Rev

/-! # join の反転における切断の計算

概要：順序写像と単体集合の反転を、空次数を含めて扱う。
方針：頂点の順序を両端から反転し、先頭区間の逆像を後半区間の補集合と比較する。
規約：a は左区間の頂点数。使われ方：S4 の押し出しと引き戻しの双対化。

対応節は Kerodon 4.3（Tag 015M）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：有限順序写像の始域と終域を両方反転する単調写像。
方針：反転、元の写像、反転の順で合成する。
規約：空の始域も許す。使われ方：補った単体の op の引き戻し。 -/
def stableReverseOrderHom {m n : ℕ} (α : Fin m →o Fin n) : Fin m →o Fin n where
  toFun i := (α i.rev).rev
  monotone' _ _ h := by
    rw [Fin.rev_le_rev]
    exact α.monotone (by rwa [Fin.rev_le_rev])

/-- 概要：補った単体の反転前後の各次数の型の同値。
方針：空次数は一点、非空次数は Mathlib の opObjEquiv を使う。
規約：単体の頂点順序の情報は単体作用に反映される。
使われ方：join の反転の各次数の写像。 -/
def stableAugOpEquiv (K : SSet.{u}) : (r : ℕ) → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K.op r ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K r
  | 0 => Equiv.refl _
  | _ + 1 => SSet.opObjEquiv

/-- 概要：補った単体の反転の同値は反転した順序写像による引き戻しと可換。
方針：空区間の場合を分け、それ以外は op の単体作用を展開する。
規約：m と n は頂点数。使われ方：join の反転の自然性。 -/
lemma stableAugOpEquiv_naturality (K : SSet.{u}) {m n : ℕ} (α : Fin m →o Fin n)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K.op n) :
    stableAugOpEquiv K m (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K.op α x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (stableReverseOrderHom α) (stableAugOpEquiv K n x) := by
  cases m with
  | zero => rfl
  | succ m =>
    cases n with
    | zero => exact Fin.elim0 (α 0)
    | succ n => rfl

/-- 概要：反転した順序写像による切断の逆像は、反対側の切断の逆像の補集合の頂点数。
方針：反転した添字の先頭区間への所属を否定し、元の切断の特徴づけを使う。
規約：a は終域の頂点数以下。使われ方：join の左右因子の交換の自然性。 -/
lemma stablePullCut_reverse {m n : ℕ} (α : Fin m →o Fin n) (a : ℕ) (ha : a ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stableReverseOrderHom α) a = m - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (n - a) := by
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α (n - a)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.cut_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le _ _) (by omega : m - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (n - a) ≤ m)
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff]
  have hi := i.isLt
  have hα := (α i.rev).isLt
  have hiff := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff α (n - a) i.rev
  change (α i.rev).rev.val < a ↔ i.val < m - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (n - a)
  simp only [Fin.val_rev] at hiff ⊢
  omega

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

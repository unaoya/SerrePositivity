module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicCellParentLaws

/-!
概要：まとめた実親の指定面は先頭でなく、minus始点では内側、plus始点では最後となる。
方針：構成済みの実添字を二つの実親へ戻して有限順序の値を計算する。
規約：hornの位置の制約を新しい入力欄にしない。
使われ方：Riehl–Verity Lemma 4.2.10、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実付着の位置。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実親の構成した指定面は先頭の面ではない。
方針：最後の添字または実最小元の後続添字の自然数の値は正。
規約：全次数の実生成元。使われ方：Riehl–Verity §4.2の実付着の指定面の正値。 -/
lemma WalkingAdjunctionAtomicCell.parentFaceIndex_ne_zero {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (a : WalkingAdjunctionAtomicCell.{u} n X Y)
    (hnf : ¬ a.NativeFillable) : a.parentFaceIndex hnf ≠ 0 := by
  intro h
  have hv := congrArg (fun i : Fin (n + 2) => i.val) h
  cases X with
  | plus => change n + 1 = 0 at hv; omega
  | minus =>
    cases n with
    | zero => exact hnf trivial
    | succ n =>
      change (walkingAdjunctionFirstBottomMergeIndex a.chain
        (walkingAdjunctionAtomic_endpoint_cards a.chain a.atomic).2 a.nondegenerate).val + 1 = 0
        at hv
      omega

/-- 概要：実親の指定面が内側であることは、元の実生成元の始点がminusであることと同値。
方針：minusでは実最小元の有限上限を使い、plusでは実最後の添字そのものへ戻す。
規約：位置の判定を入力に置かない。使われ方：Riehl–Verity Lemma 4.2.10の二つの実付着。 -/
lemma WalkingAdjunctionAtomicCell.parentFaceIndex_lt_last_iff {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (a : WalkingAdjunctionAtomicCell.{u} n X Y)
    (hnf : ¬ a.NativeFillable) : a.parentFaceIndex hnf < Fin.last (n + 1) ↔ X = .minus := by
  cases X with
  | plus =>
    change Fin.last (n + 1) < Fin.last (n + 1) ↔ WalkingAdjunctionPoint.plus = .minus
    simp
  | minus =>
    cases n with
    | zero => exact False.elim (hnf trivial)
    | succ n =>
      have hk := (walkingAdjunctionFirstBottomMergeIndex a.chain
        (walkingAdjunctionAtomic_endpoint_cards a.chain a.atomic).2 a.nondegenerate).isLt
      change (walkingAdjunctionFirstBottomMergeIndex a.chain
        (walkingAdjunctionAtomic_endpoint_cards a.chain a.atomic).2 a.nondegenerate).val + 1 <
        n + 1 + 1 ↔ WalkingAdjunctionPoint.minus = .minus
      constructor
      · intro _; rfl
      · intro _; omega

end SerrePositivity.InfinityCategories.HA.Monads

module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicCellChild

/-!
概要：有限順序模型の非純粋な実生成元と、正の次数の純粋な実親の対応をまとめる。
方針：実最小元で同じ子を選び、構成済みの両方向の全実関手の往復を使う。
規約：原典の文字列の条件との比較は別に検収する。
使われ方：Riehl–Verity Definition 4.2.1、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの親子の組。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実親から実子を回収すると、元の非純粋な実生成元と始点へ戻る。
方針：plus始点では実最後の子、minus始点では実指定面を、元の実最小元で回収する。
規約：始点の依存和の等式。使われ方：Riehl–Verity Definition 4.2.1の実親子の往復。 -/
lemma WalkingAdjunctionAtomicCell.parent_child {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    (a.parent hnf).child (a.parent_nativeFillable hnf) = ⟨X, ⟨a, hnf⟩⟩ := by
  classical
  cases X with
  | plus =>
    cases n with
    | zero =>
      refine Sigma.ext rfl (heq_of_eq ?_)
      apply Subtype.ext
      apply ext_chain
      exact walkingAdjunctionPlusParent_child a.chain a.atomic a.nondegenerate
    | succ n =>
      have hk := walkingAdjunctionPlusParent_first_index a.chain a.atomic a.nondegenerate
      rw [(a.parent hnf).child_of_last (a.parent_nativeFillable hnf) hk]
      refine Sigma.ext rfl (heq_of_eq ?_)
      apply Subtype.ext
      apply ext_chain
      exact walkingAdjunctionPlusParent_child a.chain a.atomic a.nondegenerate
  | minus =>
    cases n with
    | zero => exact False.elim (hnf trivial)
    | succ n =>
      have hi := walkingAdjunctionFirstRefinement_first_index
        a.chain a.atomic a.nondegenerate (a.parent hnf).nondegenerate
      change walkingAdjunctionFirstBottomMergeIndex (a.parent hnf).chain
        (walkingAdjunctionAtomic_endpoint_cards _ (a.parent hnf).atomic).2
        (a.parent hnf).nondegenerate =
          (walkingAdjunctionFirstBottomMergeIndex a.chain
            (walkingAdjunctionAtomic_endpoint_cards a.chain a.atomic).2 a.nondegenerate).castSucc
        at hi
      have hne : walkingAdjunctionFirstBottomMergeIndex (a.parent hnf).chain
          (walkingAdjunctionAtomic_endpoint_cards _ (a.parent hnf).atomic).2
          (a.parent hnf).nondegenerate ≠ Fin.last (n + 1) := by
        rw [hi]
        intro h
        have hv := congrArg (fun j : Fin (n + 2) => j.val) h
        have hk := (walkingAdjunctionFirstBottomMergeIndex a.chain
          (walkingAdjunctionAtomic_endpoint_cards a.chain a.atomic).2 a.nondegenerate).isLt
        change (walkingAdjunctionFirstBottomMergeIndex a.chain
          (walkingAdjunctionAtomic_endpoint_cards a.chain a.atomic).2 a.nondegenerate).val =
          n + 1 at hv
        omega
      rw [(a.parent hnf).child_of_not_last (a.parent_nativeFillable hnf) hne]
      refine Sigma.ext rfl (heq_of_eq ?_)
      apply Subtype.ext
      apply ext_chain
      change finiteChainFace (a.parent hnf).chain
        ((walkingAdjunctionFirstBottomMergeIndex (a.parent hnf).chain
          (walkingAdjunctionAtomic_endpoint_cards _ (a.parent hnf).atomic).2
          (a.parent hnf).nondegenerate).castPred hne).succ.castSucc = a.chain
      simp only [hi, Fin.castPred_castSucc]
      exact walkingAdjunctionFirstRefinement_face a.chain a.atomic a.nondegenerate

/-- 概要：非純粋な実生成元と正の次数の純粋な実親は、構成した実親子で全単射となる。
方針：実親と実子の関数を使い、両方向の実生成元の往復の等式を適用する。
規約：現在の有限順序模型のNativeFillableを用いる。使われ方：Riehl–Verity Definition 4.2.1。 -/
def walkingAdjunctionAtomicCellParentEquiv (n : ℕ) (Y : WalkingAdjunctionPoint) :
    (Σ X : WalkingAdjunctionPoint,
      {a : WalkingAdjunctionAtomicCell.{u} n X Y // ¬ a.NativeFillable}) ≃
    {p : WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y // p.NativeFillable} where
  toFun a := ⟨a.2.val.parent a.2.property, a.2.val.parent_nativeFillable a.2.property⟩
  invFun p := p.val.child p.property
  left_inv a := by
    obtain ⟨X, a, hnf⟩ := a
    exact a.parent_child hnf
  right_inv p := by
    apply Subtype.ext
    exact p.val.child_parent p.property

end SerrePositivity.InfinityCategories.HA.Monads

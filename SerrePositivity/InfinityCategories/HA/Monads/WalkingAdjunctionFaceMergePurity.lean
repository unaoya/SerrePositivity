module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFaceMergeEdges

/-!
概要：指定した二辺に触れない内側の実面は、一つだけの底併合の全点条件を保つ。
方針：残る実辺と両実対象を元へ移す。
規約：最初の位置での純粋性にも使える全位置・全個数の法則。
使われ方：Riehl–Verity Proposition 4.2.15のfillableな面、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの面の照合。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：内側の実面で残る前の辺の、一つだけの実併合の全点条件は元と同値。
方針：実辺と両実対象の照合で純粋性を輸送する。
規約：終点の個数と全実点の値を保持。使われ方：Riehl–Verity §4.2の実面のfillable条件。 -/
lemma walkingAdjunctionInnerFace_before_pure_iff {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hj : j < k) (m : ℕ) :
    let F := finiteChainFace H k.succ.castSucc
    (walkingAdjunctionOrdinalCard .minus Y (F.obj j.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (F.obj j.castSucc)),
        (walkingAdjunctionOrderHom (F.map (homOfLE (Fin.castSucc_le_succ j))) i).val = i.val - 1) ↔
    (walkingAdjunctionOrdinalCard .minus Y (H.obj j.castSucc.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj j.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (H.map
          (homOfLE (Fin.castSucc_le_succ j.castSucc))) i).val = i.val - 1) := by
  exact walkingAdjunctionPureBottomMerge_heq
    (finiteChainFace_inner_before_obj H k j.castSucc hj.le)
    (finiteChainFace_inner_before_obj H k j.succ (by
      change j.val + 1 ≤ k.val
      exact hj)) _ _ (finiteChainFace_inner_before_edge H k j hj) m

/-- 概要：内側の実面で残る後の辺の、一つだけの実併合の全点条件は元と同値。
方針：実辺と両実対象の照合で純粋性を輸送する。
規約：終点の個数と全実点の値を保持。使われ方：Riehl–Verity §4.2の実面のfillable条件。 -/
lemma walkingAdjunctionInnerFace_after_pure_iff {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hj : k < j) (m : ℕ) :
    let F := finiteChainFace H k.succ.castSucc
    (walkingAdjunctionOrdinalCard .minus Y (F.obj j.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (F.obj j.castSucc)),
        (walkingAdjunctionOrderHom (F.map (homOfLE (Fin.castSucc_le_succ j))) i).val = i.val - 1) ↔
    (walkingAdjunctionOrdinalCard .minus Y (H.obj j.succ.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj j.succ.castSucc)),
        (walkingAdjunctionOrderHom (H.map
          (homOfLE (Fin.castSucc_le_succ j.succ))) i).val = i.val - 1) := by
  exact walkingAdjunctionPureBottomMerge_heq
    (finiteChainFace_inner_after_obj H k j.castSucc hj)
    (finiteChainFace_inner_after_obj H k j.succ (by
      change k.val < j.val + 1
      exact lt_trans hj (Nat.lt_succ_self _))) _ _ (finiteChainFace_inner_after_edge H k j hj) m

end SerrePositivity.InfinityCategories.HA.Monads

module

public import
  SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParentNondegenerate
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPrefixBottomMerge
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergeTransport
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstBottomMerge

/-!
概要：始点plusから構成した実親の最初の併合は、純粋な最後の挿入辺である。
方針：最後より前の全実辺の回収と実順序和の右区間の正値を使う。
規約：最初の位置の証人を入力に置かず、既存の実最小元との等式を示す。
使われ方：Riehl–Verity Lemma 4.1.4の最後の深さ、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の位置の検収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：始点plusからの実親で、最後より前の実辺に底の二点の併合はない。
方針：元の前置した実辺を回収して、実順序和の正値の条件を移す。
規約：全実位置、長さ0を含む。使われ方：Riehl–Verity Lemma 4.1.4の最初の位置。 -/
lemma walkingAdjunctionPlusParent_no_before_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) (j : Fin n) :
    ¬ WalkingAdjunctionBottomMergeAt (walkingAdjunctionPlusParent H ha) j.castSucc := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
    intro hj
    let L := walkingAdjunctionPlusParentPrefix H
    let B := walkingAdjunctionBottomMergeObject Y 0
    let q := walkingAdjunctionBottomMergeArrow (L.obj (Fin.last (n + 1))) 0
      (walkingAdjunctionPlusParentPrefix_last_card H ha)
    let P := walkingAdjunctionPlusParent H ha
    have hs : P.obj j.castSucc.castSucc = L.obj j.castSucc :=
      composableArrowAppend_before_obj L B q j.castSucc
    have ht : P.obj j.castSucc.succ = L.obj j.succ :=
      composableArrowAppend_before_obj L B q j.succ
    exact walkingAdjunctionPlusParentPrefix_no_bottom_merge H j
      ((walkingAdjunctionMergesBottom_heq hs ht _ _
        (composableArrowAppend_before_edge L B q j)).mp hj)

/-- 概要：始点plusからの実親の最後の辺は、一つだけの実併合の全点条件を満たす。
方針：最後の実射と両端を回収して構成済みの実併合の値を移す。
規約：終点の個数1と全点の値i↦i−1。使われ方：Riehl–Verity Lemma 4.1.4のfillable条件。 -/
lemma walkingAdjunctionPlusParent_last_pure {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).succ) = 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom ((walkingAdjunctionPlusParent H ha).map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1 := by
  let L := walkingAdjunctionPlusParentPrefix H
  let B := walkingAdjunctionBottomMergeObject Y 0
  let q := walkingAdjunctionBottomMergeArrow (L.obj (Fin.last n)) 0
    (walkingAdjunctionPlusParentPrefix_last_card H ha)
  let P := walkingAdjunctionPlusParent H ha
  have hs : P.obj (Fin.last n).castSucc = L.obj (Fin.last n) :=
    composableArrowAppend_before_obj L B q (Fin.last n)
  have ht : P.obj (Fin.last n).succ = B := composableArrowAppend_last L B q
  apply (walkingAdjunctionPureBottomMerge_heq hs ht _ q
    (composableArrowAppend_last_edge n L B q) 0).mpr
  exact ⟨walkingAdjunctionBottomMergeObject_card Y 0,
    walkingAdjunctionBottomMergeArrow_val (L.obj (Fin.last n)) 0
      (walkingAdjunctionPlusParentPrefix_last_card H ha)⟩

/-- 概要：始点plusからの実親の最後の辺は実際に底の二点を併合する。
方針：実個数2から値1の点を取り、全点条件で像0を得る。
規約：元の実位置の証人を構成。使われ方：Riehl–Verity Lemma 4.1.4の最後の深さ。 -/
lemma walkingAdjunctionPlusParent_last_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    WalkingAdjunctionBottomMergeAt (walkingAdjunctionPlusParent H ha) (Fin.last n) := by
  have hc := congrArg (walkingAdjunctionOrdinalCard .minus Y)
    (composableArrowAppend_before_obj (walkingAdjunctionPlusParentPrefix H)
      (walkingAdjunctionBottomMergeObject Y 0)
      (walkingAdjunctionBottomMergeArrow
        ((walkingAdjunctionPlusParentPrefix H).obj (Fin.last n)) 0
        (walkingAdjunctionPlusParentPrefix_last_card H ha)) (Fin.last n))
  have hl := walkingAdjunctionPlusParentPrefix_last_card H ha
  change walkingAdjunctionOrdinalCard .minus Y
    ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).castSucc) =
      walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionPlusParentPrefix H).obj (Fin.last n)) at hc
  let i : Fin (walkingAdjunctionOrdinalCard .minus Y
    ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).castSucc)) := ⟨1, by omega⟩
  exact ⟨i, rfl, (walkingAdjunctionPlusParent_last_pure H ha).2 i⟩

/-- 概要：実際に選んだ最初の併合の位置は、始点plusからの実親では最後の辺。
方針：実最小元の所属とそれより前の全辺での併合の不在を合わせる。
規約：位置を仮定せず等式として回収。使われ方：Riehl–Verity Lemma 4.1.4の最後の深さ。 -/
lemma walkingAdjunctionPlusParent_first_index {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate n) :
    walkingAdjunctionFirstBottomMergeIndex (walkingAdjunctionPlusParent H ha)
      (walkingAdjunctionAtomic_endpoint_cards _ (walkingAdjunctionPlusParent_atomic H ha)).2
      (walkingAdjunctionPlusParent_nondegenerate H ha hnd) = Fin.last n := by
  have hk := walkingAdjunctionFirstBottomMergeIndex_spec (walkingAdjunctionPlusParent H ha)
    (walkingAdjunctionAtomic_endpoint_cards _ (walkingAdjunctionPlusParent_atomic H ha)).2
    (walkingAdjunctionPlusParent_nondegenerate H ha hnd)
  have hlast (k : Fin (n + 1)) :
      WalkingAdjunctionBottomMergeAt (walkingAdjunctionPlusParent H ha) k → k = Fin.last n := by
    refine Fin.lastCases (fun _ => rfl) (fun j hj => ?_) k
    exact False.elim (walkingAdjunctionPlusParent_no_before_merge H ha j hj)
  exact hlast _ hk

end SerrePositivity.InfinityCategories.HA.Monads

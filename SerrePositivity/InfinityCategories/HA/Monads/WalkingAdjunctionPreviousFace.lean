module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPureMergeCancellation
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionDegenerateInnerWidth
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFaceFirstIndex
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionInnerFaceNondegenerate

/-!
概要：最初の純粋な併合の直前を合成し、値1が先行辺の像に入る場合の実面を検収する。
方針：実併合の証人で非退化性を回収し、前の辺では元の最小性、純粋性には実消去を使う。
規約：面の非退化性・最初の位置・非純粋性を新しい入力に置かない。
使われ方：Riehl–Verity Proposition 4.2.15の指定直前の面、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの深さの比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：値1を通る先行辺を純粋な最初の併合へ合成した実面は、非退化・非純粋で深さが減る。
方針：新しい実併合の点を作り、実面の全他辺・元の実最小元・実純粋合成の消去を使う。
規約：元のnerveの非退化性と選択した実位置の等式を結論に保持。
使われ方：Riehl–Verity Proposition 4.2.15の指定直前の面の第二の場合。 -/
lemma walkingAdjunctionPreviousFace_control {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 2))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H hlast hnd = k.succ)
    (hbc : walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.succ) + 1 =
      walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.castSucc))
    (hg : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.succ))) i).val = i.val - 1)
    (hthrough : ∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc.castSucc)),
      i.val = 1 ∧ (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = 1) :
    let F := finiteChainFace H k.succ.castSucc
    ∃ hface : ULift.up F ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1),
      walkingAdjunctionFirstBottomMergeIndex F
        (by rw [finiteChainFace_inner_last]; exact hlast) hface = k ∧
      ¬ (walkingAdjunctionOrdinalCard .minus Y (F.obj k.succ) =
          walkingAdjunctionOrdinalCard .minus Y (F.obj k.castSucc) - 2 + 1 ∧
        ∀ i, (walkingAdjunctionOrderHom
          (F.map (homOfLE (Fin.castSucc_le_succ k))) i).val = i.val - 1) := by
  let F := finiteChainFace H k.succ.castSucc
  let f := H.map (homOfLE (Fin.castSucc_le_succ k.castSucc))
  let g := H.map (homOfLE (Fin.castSucc_le_succ k.succ))
  have hs := finiteChainFace_inner_before_obj H k k.castSucc (show k.val ≤ k.val from le_rfl)
  have ht := finiteChainFace_inner_after_obj H k k.succ
    (show k.val < k.val + 1 from Nat.lt_succ_self _)
  have he := finiteChainFace_inner_merged_edge H k
  have hm : WalkingAdjunctionBottomMergeAt F k := by
    apply (walkingAdjunctionMergesBottom_heq hs ht _ _ he).mpr
    obtain ⟨i, hi, him⟩ := hthrough
    refine ⟨i, hi, ?_⟩
    rw [walkingAdjunctionOrderHom_comp]
    change (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k.succ)))
      (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) i)).val = 0
    rw [hg, him]
  have hn := (walkingAdjunctionInnerFace_nondegenerate_iff_not_isIso H k hnd).mpr
    (fun hi => hm.not_isIso
      (by have := hi; exact isIso_of_equal_objects_hom_heq hs.symm ht.symm _ _ he.symm))
  have hl : walkingAdjunctionOrdinalCard .minus Y (F.obj (Fin.last (n + 1))) = 1 := by
    rw [finiteChainFace_inner_last]
    exact hlast
  refine ⟨hn, ?_, ?_⟩
  · have hle := walkingAdjunctionFirstBottomMergeIndex_minimal F hl hn hm
    have hge : ¬ walkingAdjunctionFirstBottomMergeIndex F hl hn < k := by
      intro hik
      have hmi := (walkingAdjunctionInnerFace_before_merge_iff H k _ hik).mp
        (walkingAdjunctionFirstBottomMergeIndex_spec F hl hn)
      have ho := walkingAdjunctionFirstBottomMergeIndex_minimal H hlast hnd hmi
      rw [hidx] at ho
      change k.val + 1 ≤ (walkingAdjunctionFirstBottomMergeIndex F hl hn).val at ho
      change (walkingAdjunctionFirstBottomMergeIndex F hl hn).val < k.val at hik
      omega
    exact le_antisymm hle (le_of_not_gt hge)
  · intro hp
    have hsrc := congrArg (walkingAdjunctionOrdinalCard .minus Y) hs
    have hp' := (walkingAdjunctionPureBottomMerge_heq hs ht _ _ he
      (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc.castSucc) - 2)).mp
        (by simpa only [hsrc] using hp)
    have hf : ∀ i, i.val = 1 → (walkingAdjunctionOrderHom f i).val ≠ 0 := by
      intro i hi hz
      have ho := walkingAdjunctionFirstBottomMergeIndex_minimal H hlast hnd
        (show WalkingAdjunctionBottomMergeAt H k.castSucc from ⟨i, hi, hz⟩)
      rw [hidx] at ho
      change k.val + 1 ≤ k.val at ho
      omega
    have ha : 2 ≤ walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc.castSucc) := by
      obtain ⟨i, hi, _⟩ := hthrough
      have h := i.isLt
      omega
    exact ((walkingAdjunctionHomShape_nondegenerate_iff_no_isIso H).mp hnd k.castSucc)
      (walkingAdjunctionIsIso_of_pure_bottomMerge_comp f g ha hbc hf hg hp')

end SerrePositivity.InfinityCategories.HA.Monads

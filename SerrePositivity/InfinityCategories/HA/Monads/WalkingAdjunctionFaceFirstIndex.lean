module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFaceMergeEdges
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstBottomMerge

/-!
概要：指定の併合の二辺に触れない内側の実面で、実最初の併合位置を計算する。
方針：残る辺と合成辺の実条件を元へ戻し、元の実最小元の所属と最小性を使う。
規約：面の非退化性の下で元の選択した最小元そのものとの等式を結論にする。
使われ方：Riehl–Verity Proposition 4.2.15の深さの比較、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの順序づけ。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：最初の実併合の二辺より後で内側の面を取ると、最初の位置は変わらない。
方針：元の最初の実辺を保ち、それより前の全ての実辺で元の最小性を使う。
規約：実面も非退化である場合の、実選択の位置の等式。使われ方：Riehl–Verity §4.2。 -/
lemma walkingAdjunctionInnerFace_first_index_after {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hjk : j < k)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 2))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H hlast hnd = j.castSucc)
    (hface : ULift.up (finiteChainFace H k.succ.castSucc) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    walkingAdjunctionFirstBottomMergeIndex (finiteChainFace H k.succ.castSucc)
      (by rw [finiteChainFace_inner_last]; exact hlast) hface = j := by
  let F := finiteChainFace H k.succ.castSucc
  have hl : walkingAdjunctionOrdinalCard .minus Y (F.obj (Fin.last (n + 1))) = 1 := by
    rw [finiteChainFace_inner_last]
    exact hlast
  let i := walkingAdjunctionFirstBottomMergeIndex F hl hface
  have hm : WalkingAdjunctionBottomMergeAt H j.castSucc := by
    have h := walkingAdjunctionFirstBottomMergeIndex_spec H hlast hnd
    rw [hidx] at h
    exact h
  have hj : WalkingAdjunctionBottomMergeAt F j :=
    (walkingAdjunctionInnerFace_before_merge_iff H k j hjk).mpr hm
  have hle : i ≤ j := walkingAdjunctionFirstBottomMergeIndex_minimal F hl hface hj
  have hn : ¬ i < j := by
    intro hij
    have hik : i < k := lt_trans hij hjk
    have hi := (walkingAdjunctionInnerFace_before_merge_iff H k i hik).mp
      (walkingAdjunctionFirstBottomMergeIndex_spec F hl hface)
    have ho := walkingAdjunctionFirstBottomMergeIndex_minimal H hlast hnd hi
    rw [hidx] at ho
    change j.val ≤ i.val at ho
    change i.val < j.val at hij
    omega
  exact le_antisymm hle (le_of_not_gt hn)

/-- 概要：最初の実併合より前の内側の面の合成辺に、新しい実併合はない。
方針：面の辺を前・合成・後へ分け、それぞれの元の辺で最初の位置の最小性を使う。
規約：原子性も面の非退化性も使わない。使われ方：Riehl–Verity §4.2の早い深さの比較。 -/
lemma walkingAdjunctionInnerFace_no_earlier_merge_before {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hkj : k < j)
    (hmin : ∀ r, WalkingAdjunctionBottomMergeAt H r → j.succ ≤ r)
    (r : Fin (n + 1)) (hrj : r < j) :
    ¬ WalkingAdjunctionBottomMergeAt (finiteChainFace H k.succ.castSucc) r := by
  have hn (s : Fin (n + 2)) (hs : s.val < j.val + 1) :
      ¬ WalkingAdjunctionBottomMergeAt H s := by
    intro hm
    have h := hmin s hm
    change j.val + 1 ≤ s.val at h
    omega
  rcases lt_trichotomy r k with hrk | hrk | hrk
  · intro hm
    exact hn r.castSucc (by change r.val < j.val + 1; omega)
      ((walkingAdjunctionInnerFace_before_merge_iff H k r hrk).mp hm)
  · subst r
    exact walkingAdjunctionInnerFace_no_merged_merge H k
      (hn k.castSucc (by change k.val < j.val + 1; omega))
      (hn k.succ (by change k.val + 1 < j.val + 1; exact Nat.succ_lt_succ hkj))
  · intro hm
    exact hn r.succ (by change r.val + 1 < j.val + 1; exact Nat.succ_lt_succ hrj)
      ((walkingAdjunctionInnerFace_after_merge_iff H k r hrk).mp hm)

/-- 概要：最初の実併合の前の二辺を合成する内側の面では、最初の位置は一つ減る。
方針：残る最初の実辺と、先行する全実辺での実併合の不在から実最小元を特定する。
規約：実面も非退化である場合の実位置の等式。使われ方：Riehl–Verity §4.2の深さの減少。 -/
lemma walkingAdjunctionInnerFace_first_index_before {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hkj : k < j)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 2))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H hlast hnd = j.succ)
    (hface : ULift.up (finiteChainFace H k.succ.castSucc) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    walkingAdjunctionFirstBottomMergeIndex (finiteChainFace H k.succ.castSucc)
      (by rw [finiteChainFace_inner_last]; exact hlast) hface = j := by
  let F := finiteChainFace H k.succ.castSucc
  have hl : walkingAdjunctionOrdinalCard .minus Y (F.obj (Fin.last (n + 1))) = 1 := by
    rw [finiteChainFace_inner_last]
    exact hlast
  let i := walkingAdjunctionFirstBottomMergeIndex F hl hface
  have hm : WalkingAdjunctionBottomMergeAt H j.succ := by
    have h := walkingAdjunctionFirstBottomMergeIndex_spec H hlast hnd
    rw [hidx] at h
    exact h
  have hmin (r) (hr : WalkingAdjunctionBottomMergeAt H r) : j.succ ≤ r := by
    have h := walkingAdjunctionFirstBottomMergeIndex_minimal H hlast hnd hr
    rw [hidx] at h
    exact h
  have hj := (walkingAdjunctionInnerFace_after_merge_iff H k j hkj).mpr hm
  have hle : i ≤ j := walkingAdjunctionFirstBottomMergeIndex_minimal F hl hface hj
  have hn : ¬ i < j := by
    intro hij
    exact walkingAdjunctionInnerFace_no_earlier_merge_before H k j hkj hmin i hij
      (walkingAdjunctionFirstBottomMergeIndex_spec F hl hface)
  exact le_antisymm hle (le_of_not_gt hn)

end SerrePositivity.InfinityCategories.HA.Monads

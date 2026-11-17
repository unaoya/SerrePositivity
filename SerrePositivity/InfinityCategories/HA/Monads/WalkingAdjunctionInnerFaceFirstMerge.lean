module

public import
  SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionInnerFaceNondegenerate
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstBottomMerge

/-!
概要：内側の面の最初の実併合の位置を、元の実親の最初の位置から回収する。
方針：指定合成辺の実併合と、先行辺の実射の照合・実最小元の最小性を合わせる。
規約：元の実選択の位置を、子の新しい証人へ置き換えない。
使われ方：Riehl–Verity Lemma 4.1.3の実親の逆方向、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の最初の実位置の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：指定した内側の位置が最初の実位置なら、親のその辺に実併合がある。
方針：構成済みの実最小元の所属を位置の等式で移す。
規約：実証人を構成した最小元から取る。使われ方：Riehl–Verity Lemma 4.1.3の実面。 -/
lemma walkingAdjunctionInnerFace_first_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = k.castSucc) :
    WalkingAdjunctionBottomMergeAt P k.castSucc := by
  have hm := walkingAdjunctionFirstBottomMergeIndex_spec P
    (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd
  rw [hidx] at hm
  exact hm

/-- 概要：最初の内側の実併合を合成した子には、それより前の実併合はない。
方針：先行実辺を親の実辺へ戻し、親の実最小元の最小性を使う。
規約：全ての先行実位置。使われ方：Riehl–Verity Lemma 4.1.3の子の実最小元。 -/
lemma walkingAdjunctionInnerFace_no_before_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = k.castSucc)
    (j : Fin (n + 1)) (hj : j < k) :
    ¬ WalkingAdjunctionBottomMergeAt (finiteChainFace P k.succ.castSucc) j := by
  intro hm
  have hs := finiteChainFace_inner_before_obj P k j.castSucc (by
    change j.val ≤ k.val
    exact hj.le)
  have ht := finiteChainFace_inner_before_obj P k j.succ (by
    change j.val + 1 ≤ k.val
    exact hj)
  have hp := (walkingAdjunctionMergesBottom_heq hs ht _ _
    (finiteChainFace_inner_before_edge P k j hj)).mp hm
  have he := walkingAdjunctionFirstBottomMergeIndex_minimal P
    (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd hp
  rw [hidx] at he
  change k.val ≤ j.val at he
  change j.val < k.val at hj
  omega

/-- 概要：最初の内側の併合を合成した子の、実際に選んだ最初の位置は指定位置。
方針：指定辺の実併合で最小元を上から押さえ、先行する全辺の併合を排除する。
規約：元の有限最小元との等式。使われ方：Riehl–Verity Lemma 4.1.3の実親の回収。 -/
lemma walkingAdjunctionInnerFace_first_index {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = k.castSucc) :
    walkingAdjunctionFirstBottomMergeIndex (finiteChainFace P k.succ.castSucc)
      (walkingAdjunctionAtomic_endpoint_cards _ (walkingAdjunctionInnerFace_atomic P k ha)).2
      (walkingAdjunctionInnerFace_nondegenerate P k hnd
        (walkingAdjunctionInnerFace_first_merge P k ha hnd hidx)) = k := by
  let H := finiteChainFace P k.succ.castSucc
  let hlast := (walkingAdjunctionAtomic_endpoint_cards _
    (walkingAdjunctionInnerFace_atomic P k ha)).2
  let hnon := walkingAdjunctionInnerFace_nondegenerate P k hnd
    (walkingAdjunctionInnerFace_first_merge P k ha hnd hidx)
  have hm := walkingAdjunctionInnerFace_merge P k
    (walkingAdjunctionInnerFace_first_merge P k ha hnd hidx)
  have hle := walkingAdjunctionFirstBottomMergeIndex_minimal H hlast hnon hm
  have hn : ¬ walkingAdjunctionFirstBottomMergeIndex H hlast hnon < k := by
    intro hj
    exact walkingAdjunctionInnerFace_no_before_merge P k ha hnd hidx _ hj
      (walkingAdjunctionFirstBottomMergeIndex_spec H hlast hnon)
  exact le_antisymm hle (le_of_not_gt hn)

end SerrePositivity.InfinityCategories.HA.Monads

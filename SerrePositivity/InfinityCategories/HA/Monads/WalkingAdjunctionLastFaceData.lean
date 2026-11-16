module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowLastFace
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParentPositions

/-!
概要：最初の実併合が純粋な最後の辺である原子から、最後の面の回収条件を供給する。
方針：実最小元の最小性で先行する併合を除き、原子の終点と純粋性で二点を回収する。
規約：逆方向に必要な条件を新しい存在の仮定へ置き換えない。
使われ方：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の最後の実面の検収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：最初の実併合が最後の辺なら、それより前には実併合がない。
方針：実最小元の最小性と有限添字の最後の点の最大性を使う。
規約：全先行実位置。使われ方：Riehl–Verity Lemma 4.1.4の逆方向の実面。 -/
lemma walkingAdjunctionNoMerge_before_last_of_first_last {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n) (j : Fin n) :
    ¬ WalkingAdjunctionBottomMergeAt P j.castSucc := by
  intro hj
  have he := walkingAdjunctionFirstBottomMergeIndex_minimal P
    (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd hj
  rw [hidx] at he
  change n ≤ j.val at he
  have hjlt := j.isLt
  omega

/-- 概要：最初の実併合が最後の辺なら、最後の実面の全辺が二番目の点を0へ送らない。
方針：最後の実面の元の辺を回収し、実最小元より前の併合の不在を移す。
規約：長さ0を含む全隣接辺の実条件。使われ方：Riehl–Verity Lemma 4.1.4の実因子の回収。 -/
lemma walkingAdjunctionLastFace_no_one_of_first_last {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n) :
    ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y
      ((finiteChainFace P (Fin.last (n + 1))).obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        ((finiteChainFace P (Fin.last (n + 1))).map
          (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0 := by
  intro k a hak hz
  cases n with
  | zero => exact Fin.elim0 k
  | succ n =>
    apply walkingAdjunctionNoMerge_before_last_of_first_last P ha hnd hidx k
    exact (walkingAdjunctionMergesBottom_heq
      (finiteChainFace_last_obj P k.castSucc) (finiteChainFace_last_obj P k.succ) _ _
      (finiteChainFace_last_edge P k)).mp ⟨a, hak, hz⟩

/-- 概要：純粋な最初の実併合が最後の辺なら、その直前の実対象の個数は2。
方針：併合の実証人から二点以上を得て、原子の終点1と純粋性の個数を合わせる。
規約：最後の実面の実終点の個数。使われ方：Riehl–Verity Lemma 4.1.4の逆方向。 -/
lemma walkingAdjunctionLastFace_card_two_of_first_last_pure {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = Fin.last n)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1) :
    walkingAdjunctionOrdinalCard .minus Y
      ((finiteChainFace P (Fin.last (n + 1))).obj (Fin.last n)) = 2 := by
  have hm := walkingAdjunctionFirstBottomMergeIndex_spec P
    (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd
  rw [hidx] at hm
  have hc := hm.card_two_le
  have ht := (walkingAdjunctionAtomic_endpoint_cards P ha).2
  have hv := hp.1
  rw [finiteChainFace_last_obj]
  change walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).succ) = 1 at ht
  omega

end SerrePositivity.InfinityCategories.HA.Monads

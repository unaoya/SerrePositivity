module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowInnerFace
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergeTransport
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionIsoDegeneracy
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicEndpoints

/-!
概要：内側の実親の指定面は原子的・非退化で、指定辺は実際に底の二点を併合する。
方針：指定二辺の合成と最小元保存で併合を回収し、他の辺は元の非同型辺に戻す。
規約：元のHomのnerveの非退化性を証明する。
使われ方：Riehl–Verity Lemma 4.1.3の実親の逆方向、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実子の検収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：底の二点を併合する元の実辺は同型ではない。
方針：実同型の点の値の保存と値1の証人を比較する。
規約：元のHomの同型性を否定。使われ方：Riehl–Verity Lemma 4.1.3の合成辺。 -/
lemma WalkingAdjunctionBottomMergeAt.not_isIso {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)} {k : Fin (n + 1)}
    (h : WalkingAdjunctionBottomMergeAt H k) :
    ¬ IsIso (H.map (homOfLE (Fin.castSucc_le_succ k))) := by
  intro hi
  have := hi
  obtain ⟨i, hi, hz⟩ := h
  have he := walkingAdjunctionOrderHom_val_of_isIso
    (H.map (homOfLE (Fin.castSucc_le_succ k))) i
  omega

/-- 概要：原子的な実全単体の内側の面は原子的。
方針：元の実始点・実終点を回収し、端点による原子性の判定へ戻す。
規約：子の原子性を入力にしない。使われ方：Riehl–Verity Lemma 4.1.3の実子。 -/
lemma walkingAdjunctionInnerFace_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩)
      (finiteChainFace P k.succ.castSucc) := by
  apply walkingAdjunctionAtomic_of_endpoint_cards
  · exact (congrArg (walkingAdjunctionOrdinalCard .minus Y)
      (finiteChainFace_first P k.castSucc)).trans (walkingAdjunctionAtomic_endpoint_cards P ha).1
  · exact (congrArg (walkingAdjunctionOrdinalCard .minus Y)
      (finiteChainFace_inner_last P k)).trans (walkingAdjunctionAtomic_endpoint_cards P ha).2

/-- 概要：内側の面の合成辺は、左の元の実辺が併合するなら実際に併合する。
方針：左の実併合の証人を右の射の最小元保存で送り、実合成辺へ戻す。
規約：子の実併合の証人を構成。使われ方：Riehl–Verity Lemma 4.1.3の実逆。 -/
lemma walkingAdjunctionInnerFace_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hm : WalkingAdjunctionBottomMergeAt P k.castSucc) :
    WalkingAdjunctionBottomMergeAt (finiteChainFace P k.succ.castSucc) k := by
  have hs := finiteChainFace_inner_before_obj P k k.castSucc (by exact le_rfl)
  have ht := finiteChainFace_inner_after_obj P k k.succ (by change k.val < k.val + 1; omega)
  apply (walkingAdjunctionMergesBottom_heq hs ht _ _
    (finiteChainFace_inner_merged_edge P k)).mpr
  obtain ⟨i, hi, hz⟩ := hm
  refine ⟨i, hi, ?_⟩
  rw [walkingAdjunctionOrderHom_comp]
  exact walkingAdjunctionOrderHom_bottom (P.map (homOfLE (Fin.castSucc_le_succ k.succ))) _ hz

/-- 概要：非退化な実親の内側の面は、左の元の辺が併合するなら非退化。
方針：指定合成辺は実併合で非同型とし、他の実辺は親の非同型辺へ戻す。
規約：元のHomのnerveの非退化性。使われ方：Riehl–Verity Lemma 4.1.3の実子の検収。 -/
lemma walkingAdjunctionInnerFace_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hm : WalkingAdjunctionBottomMergeAt P k.castSucc) :
    ULift.up (finiteChainFace P k.succ.castSucc) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1) := by
  let H := finiteChainFace P k.succ.castSucc
  have hp := (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso P).mp hnd
  apply (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso H).mpr
  intro j hj
  have := hj
  rcases lt_trichotomy j k with hlt | rfl | hgt
  · apply hp j.castSucc
    have hs : H.obj j.castSucc = P.obj j.castSucc.castSucc :=
      finiteChainFace_inner_before_obj P k _ (by change j.val ≤ k.val; exact hlt.le)
    have ht : H.obj j.succ = P.obj j.castSucc.succ :=
      finiteChainFace_inner_before_obj P k _ (by change j.val + 1 ≤ k.val; exact hlt)
    exact isIso_of_equal_objects_hom_heq hs ht _ _ (finiteChainFace_inner_before_edge P k j hlt)
  · exact (walkingAdjunctionInnerFace_merge P j hm).not_isIso hj
  · apply hp j.succ
    have hs : H.obj j.castSucc = P.obj j.succ.castSucc :=
      finiteChainFace_inner_after_obj P k _ hgt
    have ht : H.obj j.succ = P.obj j.succ.succ :=
      finiteChainFace_inner_after_obj P k _ (by
        change k.val < j.val + 1
        have hv : k.val < j.val := hgt
        omega)
    exact isIso_of_equal_objects_hom_heq hs ht _ _ (finiteChainFace_inner_after_edge P k j hgt)

end SerrePositivity.InfinityCategories.HA.Monads

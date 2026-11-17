module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowInnerFace
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergeTransport

/-!
概要：内側の実面の全辺について、底の二点の併合を元の辺へ戻す。
方針：残る辺は実射の輸送、合成辺は0を反映する有限単調射の合成で扱う。
規約：原子性・非退化性を使わず、元の全実鎖に証明する。
使われ方：Riehl–Verity Proposition 4.2.15の深さの比較、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの面の法則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：二点目の像0のない二つの有限単調射を合成しても、二点目の像0は生じない。
方針：どちらも0の逆像を反映することを合成する。
規約：空の有限順序を含む。使われ方：Riehl–Verity §4.2の先行する合成辺の検収。 -/
lemma ordinalNoOneZero_comp {a b c : ℕ} (f : Fin a →o Fin b) (g : Fin b →o Fin c)
    (hf : ∀ i : Fin a, i.val = 1 → (f i).val ≠ 0)
    (hg : ∀ i : Fin b, i.val = 1 → (g i).val ≠ 0) :
    ∀ i : Fin a, i.val = 1 → (g.comp f i).val ≠ 0 := by
  intro i hi hz
  have hb := ordinalReflectsZero_of_no_one g hg (f i) hz
  exact hf i hi hb

/-- 概要：内側の実面の前の辺での実併合は、元の同じ実辺での併合と同値。
方針：元の実両端と実射の異種等式へ移す。
規約：全先行位置。使われ方：Riehl–Verity §4.2の実最初の位置の比較。 -/
lemma walkingAdjunctionInnerFace_before_merge_iff {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hj : j < k) :
    WalkingAdjunctionBottomMergeAt (finiteChainFace H k.succ.castSucc) j ↔
      WalkingAdjunctionBottomMergeAt H j.castSucc := by
  exact walkingAdjunctionMergesBottom_heq
    (finiteChainFace_inner_before_obj H k j.castSucc (by exact hj.le))
    (finiteChainFace_inner_before_obj H k j.succ (by
      change j.val + 1 ≤ k.val
      exact hj)) _ _ (finiteChainFace_inner_before_edge H k j hj)

/-- 概要：内側の実面の後の辺での実併合は、元の一つ後の実辺での併合と同値。
方針：元の実両端と実射の異種等式へ移す。
規約：全後続位置。使われ方：Riehl–Verity §4.2の実最初の位置の比較。 -/
lemma walkingAdjunctionInnerFace_after_merge_iff {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2))
    (k j : Fin (n + 1)) (hj : k < j) :
    WalkingAdjunctionBottomMergeAt (finiteChainFace H k.succ.castSucc) j ↔
      WalkingAdjunctionBottomMergeAt H j.succ := by
  exact walkingAdjunctionMergesBottom_heq
    (finiteChainFace_inner_after_obj H k j.castSucc hj)
    (finiteChainFace_inner_after_obj H k j.succ (by
      change k.val < j.val + 1
      exact lt_trans hj (Nat.lt_succ_self _))) _ _
    (finiteChainFace_inner_after_edge H k j hj)

/-- 概要：元の二辺で実併合がなければ、内側の実面の合成辺でも実併合はない。
方針：合成辺の実表示を戻し、0を反映する実有限単調射の合成を使う。
規約：全実鎖、原子性を要求しない。使われ方：Riehl–Verity §4.2の深さが早まらない条件。 -/
lemma walkingAdjunctionInnerFace_no_merged_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hf : ¬ WalkingAdjunctionBottomMergeAt H k.castSucc)
    (hg : ¬ WalkingAdjunctionBottomMergeAt H k.succ) :
    ¬ WalkingAdjunctionBottomMergeAt (finiteChainFace H k.succ.castSucc) k := by
  have he := walkingAdjunctionMergesBottom_heq
    (finiteChainFace_inner_before_obj H k k.castSucc (by exact le_rfl))
    (finiteChainFace_inner_after_obj H k k.succ (by change k.val < k.val + 1; omega))
    _ _ (finiteChainFace_inner_merged_edge H k)
  intro hm
  obtain ⟨i, hi, hz⟩ := he.mp hm
  rw [walkingAdjunctionOrderHom_comp] at hz
  exact ordinalNoOneZero_comp _ _ (fun i hi hz => hf ⟨i, hi, hz⟩)
    (fun i hi hz => hg ⟨i, hi, hz⟩) i hi hz

end SerrePositivity.InfinityCategories.HA.Monads

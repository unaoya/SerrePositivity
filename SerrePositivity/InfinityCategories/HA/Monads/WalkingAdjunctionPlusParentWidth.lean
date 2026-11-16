module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalAppendVariation
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthAppend
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParent
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergeLaws

/-!
概要：始点plusから構成した実親の有限順序の幅は、元の幅より1大きい。
方針：生成射の前置は辺の変化量を保ち、実終端の併合の変化量は1であることを使う。
規約：幅の増分を親の新しい入力に置かない。文字列との全比較は別に行う。
使われ方：Riehl–Verity Lemma 4.1.4・Proposition 4.2.15の実親の幅、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実生成射を前置した辺の変化量は元の辺の変化量。
方針：実順序和の変化量の加法性と恒等射の変化量0を使う。
規約：全実辺、長さ0も含む。使われ方：Riehl–Verity §4.2の前置の幅。 -/
lemma walkingAdjunctionPlusParentPrefix_variation {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n) (j : Fin n) :
    ordinalMapVariation (walkingAdjunctionOrderHom ((walkingAdjunctionPlusParentPrefix H).map
      (homOfLE (Fin.castSucc_le_succ j)))) =
      ordinalMapVariation (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ j)))) := by
  let U := walkingAdjunctionGeneratorVertex .minus
  let f := H.map (homOfLE (Fin.castSucc_le_succ j))
  have he := walkingAdjunctionOrderHom_comp_plus .minus Y (𝟙 U) f
  have hv := ordinalMapVariation_heq (walkingAdjunctionPlusParentPrefix_card H j.castSucc)
    (walkingAdjunctionPlusParentPrefix_card H j.succ) _ _ he
  change ordinalMapVariation (walkingAdjunctionOrderHom
    ((walkingAdjunctionPlusParentPrefix H).map (homOfLE (Fin.castSucc_le_succ j)))) = _ at hv
  rw [hv, ordinalMapVariation_append, walkingAdjunctionOrderHom_id,
    ordinalMapVariation_id, zero_add]

/-- 概要：実生成射の前置で有限順序の幅は1増える。
方針：全実辺の変化量は保たれ、両端の個数と始点の補正だけが変わる。
規約：原子性を仮定しない全実鎖。使われ方：Riehl–Verity §4.2の最後の深さの幅。 -/
lemma walkingAdjunctionPlusParentPrefix_ordinalWidth {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParentPrefix H) =
      walkingAdjunctionOrdinalWidth H + 1 := by
  have hs : (∑ j : Fin n, ordinalMapVariation (walkingAdjunctionOrderHom
        ((walkingAdjunctionPlusParentPrefix H).map (homOfLE (Fin.castSucc_le_succ j))))) =
      ∑ j : Fin n, ordinalMapVariation
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j)))) :=
    Finset.sum_congr rfl (fun j _ => walkingAdjunctionPlusParentPrefix_variation H j)
  have hb := walkingAdjunctionCard_pair_corrections_le .plus Y (H.obj 0) (H.obj (Fin.last n))
  let s := ∑ j : Fin n, ordinalMapVariation
    (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j))))
  unfold walkingAdjunctionOrdinalWidth
  rw [hs, walkingAdjunctionPlusParentPrefix_card, walkingAdjunctionPlusParentPrefix_card]
  change (1 + walkingAdjunctionOrdinalCard .plus Y (H.obj 0) +
      (1 + walkingAdjunctionOrdinalCard .plus Y (H.obj (Fin.last n))) -
        (1 + walkingAdjunctionTargetCorrection Y) + s) =
    (walkingAdjunctionOrdinalCard .plus Y (H.obj 0) +
      walkingAdjunctionOrdinalCard .plus Y (H.obj (Fin.last n)) -
        (0 + walkingAdjunctionTargetCorrection Y) + s) + 1
  change 0 + walkingAdjunctionTargetCorrection Y ≤
    walkingAdjunctionOrdinalCard .plus Y (H.obj 0) +
      walkingAdjunctionOrdinalCard .plus Y (H.obj (Fin.last n)) at hb
  omega

/-- 概要：構成済みの実底併合射の変化量は1。
方針：実全射性から像の個数を終点の個数へ戻し、両端の実個数を計算する。
規約：元の実射の変化量。使われ方：Riehl–Verity §4.2の最後の挿入辺の幅。 -/
lemma walkingAdjunctionBottomMergeArrow_variation {Y : WalkingAdjunctionPoint}
    (A : walkingAdjunctionHom .minus Y) (m : ℕ)
    (hA : walkingAdjunctionOrdinalCard .minus Y A = m + 2) :
    ordinalMapVariation (walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA)) =
      1 := by
  have hi := (ordinalImageCard_eq_target_iff
    (walkingAdjunctionOrderHom (walkingAdjunctionBottomMergeArrow A m hA))).mpr
      (walkingAdjunctionBottomMergeArrow_surjective A m hA)
  unfold ordinalMapVariation
  rw [hi, hA, walkingAdjunctionBottomMergeObject_card]
  omega

/-- 概要：始点plusの実原子から構成した実親の有限順序の幅は元の幅より1大きい。
方針：実前置の幅の増分と、終点2から1への実併合の終端挿入の幅の式を合わせる。
規約：構成済みの実親への法則。使われ方：Riehl–Verity Lemma 4.1.4の実幅の検収。 -/
lemma walkingAdjunctionPlusParent_ordinalWidth {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent H ha) =
      walkingAdjunctionOrdinalWidth H + 1 := by
  let L := walkingAdjunctionPlusParentPrefix H
  let B := walkingAdjunctionBottomMergeObject Y 0
  let q := walkingAdjunctionBottomMergeArrow (L.obj (Fin.last n)) 0
    (walkingAdjunctionPlusParentPrefix_last_card H ha)
  have hw := walkingAdjunctionOrdinalWidth_append L B q
  have hl := walkingAdjunctionPlusParentPrefix_ordinalWidth H
  have hc := walkingAdjunctionPlusParentPrefix_last_card H ha
  have hb := walkingAdjunctionBottomMergeObject_card Y 0
  have hv := walkingAdjunctionBottomMergeArrow_variation (L.obj (Fin.last n)) 0
    (walkingAdjunctionPlusParentPrefix_last_card H ha)
  change walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent H ha) +
    walkingAdjunctionOrdinalCard .minus Y (L.obj (Fin.last n)) =
      walkingAdjunctionOrdinalWidth L + walkingAdjunctionOrdinalCard .minus Y B +
        ordinalMapVariation (walkingAdjunctionOrderHom q) at hw
  change walkingAdjunctionOrdinalWidth L = walkingAdjunctionOrdinalWidth H + 1 at hl
  change walkingAdjunctionOrdinalCard .minus Y (L.obj (Fin.last n)) = 2 at hc
  change walkingAdjunctionOrdinalCard .minus Y B = 1 at hb
  change ordinalMapVariation (walkingAdjunctionOrderHom q) = 1 at hv
  omega

end SerrePositivity.InfinityCategories.HA.Monads

module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthPrecomp
public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowAppendPositions

/-!
概要：実全鎖の終端へ実射を挿入したときの、有限順序の幅の変化を計算する。
方針：元の全実辺と最後の実辺を回収し、辺の変化量の有限和を分ける。
規約：対象と全射の実照合を含む。文字列の幅との全比較は別に行う。
使われ方：Riehl–Verity Proposition 4.2.15の最後の深さの実親の幅、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実挿入の幅の法則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：終端への実挿入より前の実辺の変化量は元のものと一致する。
方針：元の全実対象と実辺を回収し、変化量を係数移送する。
規約：長さ0も含む全先行実辺。使われ方：Riehl–Verity §4.2の終端挿入。 -/
lemma walkingAdjunctionAppend_before_variation {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (B : walkingAdjunctionHom X Y)
    (f : H.obj (Fin.last n) ⟶ B) (j : Fin n) :
    ordinalMapVariation (walkingAdjunctionOrderHom ((composableArrowAppend H B f).map
      (homOfLE (Fin.castSucc_le_succ j.castSucc)))) =
    ordinalMapVariation (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j)))) := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
    exact walkingAdjunctionMapVariation_heq (composableArrowAppend_before_obj H B f j.castSucc)
      (composableArrowAppend_before_obj H B f j.succ) _ _
      (composableArrowAppend_before_edge H B f j)

/-- 概要：終端へ挿入した最後の実辺の変化量は指定実射の変化量。
方針：最後の実両端と実射を回収し、変化量を移す。
規約：元の実射を保持する。使われ方：Riehl–Verity §4.2の最後の実辺の幅。 -/
lemma walkingAdjunctionAppend_last_variation {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (B : walkingAdjunctionHom X Y)
    (f : H.obj (Fin.last n) ⟶ B) :
    ordinalMapVariation (walkingAdjunctionOrderHom ((composableArrowAppend H B f).map
      (homOfLE (Fin.castSucc_le_succ (Fin.last n))))) =
      ordinalMapVariation (walkingAdjunctionOrderHom f) :=
  walkingAdjunctionMapVariation_heq (composableArrowAppend_before_obj H B f (Fin.last n))
    (composableArrowAppend_last H B f) _ _ (composableArrowAppend_last_edge n H B f)

/-- 概要：終端への実挿入の全辺の変化量の和は、元の和に最後の実射の変化量を加えたもの。
方針：有限和を最後の添字で分け、実辺の変化量の回収を使う。
規約：全実辺を含む。使われ方：Riehl–Verity §4.2の終端挿入の幅の式。 -/
lemma walkingAdjunctionAppend_variation_sum {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (B : walkingAdjunctionHom X Y)
    (f : H.obj (Fin.last n) ⟶ B) :
    (∑ j : Fin (n + 1), ordinalMapVariation
      (walkingAdjunctionOrderHom ((composableArrowAppend H B f).map
        (homOfLE (Fin.castSucc_le_succ j))))) =
      (∑ j : Fin n, ordinalMapVariation
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j))))) +
          ordinalMapVariation (walkingAdjunctionOrderHom f) := by
  rw [Fin.sum_univ_castSucc]
  simp only [walkingAdjunctionAppend_before_variation, walkingAdjunctionAppend_last_variation]

/-- 概要：終端へ実射を挿入したときの有限順序の幅を、実両端と変化量で比較する。
方針：実両端と全辺の変化量の和を回収し、補正の減算の範囲を使う。
規約：空の実対象も含む。使われ方：Riehl–Verity §4.2の最後の深さの実親の幅。 -/
lemma walkingAdjunctionOrdinalWidth_append {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) (B : walkingAdjunctionHom X Y)
    (f : H.obj (Fin.last n) ⟶ B) :
    walkingAdjunctionOrdinalWidth (composableArrowAppend H B f) +
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) =
    walkingAdjunctionOrdinalWidth H + walkingAdjunctionOrdinalCard X Y B +
      ordinalMapVariation (walkingAdjunctionOrderHom f) := by
  have hh := walkingAdjunctionCard_pair_corrections_le X Y (H.obj 0) (H.obj (Fin.last n))
  have hp := walkingAdjunctionCard_pair_corrections_le X Y (H.obj 0) B
  unfold walkingAdjunctionOrdinalWidth
  rw [walkingAdjunctionAppend_variation_sum, composableArrowAppend_first,
    composableArrowAppend_last]
  omega

end SerrePositivity.InfinityCategories.HA.Monads

module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionEndpointSizes

/-!
概要：原子的な全単体の始頂点と終頂点の有限個数を決定する。
方針：余分な点があれば端点から内側の実切れ目を作り、原子性と矛盾させる。
規約：内側の切れ目の実分解は構成済みのものを使う。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の有限端点による表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {n : ℕ} {X Y : WalkingAdjunctionPoint}
  (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)

/-- 概要：原子的な全単体の終頂点の実点の個数は1以下。
方針：二点以上あれば値1のplusの切れ目が両外端の厳密な内側にある。
規約：元の原子性と構成済みの切れ目を使う。使われ方：Riehl–Verity §4.1。 -/
lemma walkingAdjunctionAtomic_last_card_le_one
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) ≤ 1 := by
  by_contra hn
  have hp : 1 < walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) := by omega
  let t : Fin (walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) + 1) := ⟨1, by omega⟩
  let a := WalkingAdjunctionPlusCut.ofLast H t
  have ha : (a.value (Fin.last n)).val = 1 :=
    congrArg Fin.val (WalkingAdjunctionPlusCut.ofLast_value_last H t)
  have hl : X = .minus → 0 < (a.value (Fin.last n)).val := by intro _; omega
  have hr : Y = .minus → (a.value (Fin.last n)).val <
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) := by intro _; omega
  rcases ((walkingAdjunctionLevelIsAtomic_iff_boundary_cuts H).mp h).2 .plus a
      (a.source_le hl) (a.le_target hr) with hs | ht
  · have hs := hs (Fin.last n)
    rw [walkingAdjunctionSourceCut_rank] at hs
    change 2 * (a.value (Fin.last n)).val + 0 = walkingAdjunctionTargetCorrection X at hs
    have hx : walkingAdjunctionTargetCorrection X ≤ 1 := by cases X <;> decide
    omega
  · have ht := ht (Fin.last n)
    have hc := walkingAdjunctionTargetCut_rank_card H (Fin.last n)
    change 2 * (a.value (Fin.last n)).val + 0 =
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) (Fin.last n) at ht
    have hy : walkingAdjunctionTargetCorrection Y ≤ 1 := by cases Y <;> decide
    omega

/-- 概要：原子的な全単体の始頂点の個数は両端の補正の和以下。
方針：余分な点があれば始点の補正を座標に持つminusの共有点が厳密に内側にある。
規約：全共有点の実分解を用いる。使われ方：Riehl–Verity §4.1。 -/
lemma walkingAdjunctionAtomic_first_card_le_corrections
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard X Y (H.obj 0) ≤
      walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y := by
  by_contra hn
  have hp : walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y <
      walkingAdjunctionOrdinalCard X Y (H.obj 0) := by omega
  let t : Fin (walkingAdjunctionOrdinalCard X Y (H.obj 0)) :=
    ⟨walkingAdjunctionTargetCorrection X, by omega⟩
  let a := WalkingAdjunctionMinusCut.ofFirst H t
  have ha : (a.value 0).val = walkingAdjunctionTargetCorrection X :=
    congrArg Fin.val (WalkingAdjunctionMinusCut.ofFirst_value_zero H t)
  rcases ((walkingAdjunctionLevelIsAtomic_iff_boundary_cuts H).mp h).2 .minus a
      a.source_le a.le_target with hs | ht
  · have hs := hs 0
    rw [walkingAdjunctionSourceCut_rank] at hs
    change 2 * (a.value 0).val + 1 = walkingAdjunctionTargetCorrection X at hs
    omega
  · have ht := ht 0
    have hc := walkingAdjunctionTargetCut_rank_card H 0
    change 2 * (a.value 0).val + 1 =
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) 0 at ht
    omega

/-- 概要：原子的な全単体の始頂点の個数は両端の補正の和、終頂点の個数は1。
方針：原子性による上限と正の長さによる下限を合わせる。
規約：四Homを一つの型で扱う。使われ方：Riehl–Verity §4.1の原子の端点の決定。 -/
lemma walkingAdjunctionAtomic_endpoint_cards
    (h : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard X Y (H.obj 0) =
        walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y ∧
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 1 := by
  exact ⟨Nat.le_antisymm (walkingAdjunctionAtomic_first_card_le_corrections H h)
    (walkingAdjunctionFirstCard_corrections_le_of_size_pos H h.1),
    Nat.le_antisymm (walkingAdjunctionAtomic_last_card_le_one H h)
      (walkingAdjunctionLastCard_pos_of_size_pos H h.1)⟩

end SerrePositivity.InfinityCategories.HA.Monads

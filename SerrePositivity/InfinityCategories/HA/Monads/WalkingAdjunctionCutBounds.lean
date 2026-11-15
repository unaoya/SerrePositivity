module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutFactorization
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutEndpoints

/-!
概要：切れ目が実分解を与える外端の間の条件を有限端点の条件へ移す。
方針：minusの共有点は常に外端の間、plusの切れ目は終頂点の境界条件を使う。
規約：許されることを仮定せず、順位の全比較と端点の個数から証明する。
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
  {H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y}

/-- 概要：右外端の順位は元の有限点の個数と終点の補正で決まる。
方針：座標は重み、個数は重みと補正の和であることを使う。
規約：終点がminusの場合の1を保持する。使われ方：Riehl–Verity §4.1の端点の上限。 -/
lemma walkingAdjunctionTargetCut_rank_card (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (i : Fin (n + 1)) :
    walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i +
        walkingAdjunctionTargetCorrection Y = 2 * walkingAdjunctionOrdinalCard X Y (H.obj i) := by
  rw [walkingAdjunctionCutRank, walkingAdjunctionTargetCut_coordinate]
  have hc := walkingAdjunctionOrdinalCard_weight X Y (H.obj i)
  omega

/-- 概要：全てのminusの共有点は左外端以上。
方針：奇数の順位は始点の補正以上である。規約：全頂点。
使われ方：Riehl–Verity §4.1の全共有点の実分解。 -/
lemma WalkingAdjunctionMinusCut.source_le (a : WalkingAdjunctionMinusCut H) :
    ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank (M := .minus) a i := by
  intro i
  rw [walkingAdjunctionSourceCut_rank]
  change walkingAdjunctionTargetCorrection X ≤ 2 * (a.value i).val + 1
  cases X <;> simp only [walkingAdjunctionTargetCorrection] <;> omega

/-- 概要：全てのminusの共有点は右外端以下。
方針：共有点の有限個数の上限と右外端の順位を比較する。規約：全頂点。
使われ方：Riehl–Verity §4.1の全共有点の実分解。 -/
lemma WalkingAdjunctionMinusCut.le_target (a : WalkingAdjunctionMinusCut H) :
    ∀ i, walkingAdjunctionCutRank (M := .minus) a i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i := by
  intro i
  have hc := walkingAdjunctionTargetCut_rank_card H i
  have hi := (a.value i).isLt
  change 2 * (a.value i).val + 1 ≤ _
  cases Y <;> simp only [walkingAdjunctionTargetCorrection] at hc <;> omega

/-- 概要：plusの切れ目は終頂点で始点minusの外側0を避ければ左外端以上。
方針：始点plusは非負性、minusは全順位の比較と終頂点の厳密不等式を使う。
規約：全頂点の比較を結論にする。使われ方：Riehl–Verity §4.1の切れ目の実分解。 -/
lemma WalkingAdjunctionPlusCut.source_le (a : WalkingAdjunctionPlusCut H)
    (hl : X = .minus → 0 < (a.value (Fin.last n)).val) :
    ∀ i, walkingAdjunctionCutRank (walkingAdjunctionSourceCut H) i ≤
      walkingAdjunctionCutRank (M := .plus) a i := by
  cases X
  · intro i
    rw [walkingAdjunctionSourceCut_rank]
    change 0 ≤ 2 * (a.value i).val + 0
    omega
  · have hp := hl rfl
    rcases walkingAdjunctionCutRank_total (walkingAdjunctionSourceCut H) (M := .minus)
        (N := .plus) a with h | h
    · exact h
    · exfalso
      have hi := h (Fin.last n)
      rw [walkingAdjunctionSourceCut_rank] at hi
      change 2 * (a.value (Fin.last n)).val + 0 ≤ 1 at hi
      omega

/-- 概要：plusの切れ目は終頂点で終点minusの最外端を避ければ右外端以下。
方針：終点plusは点の上限、minusは全順位の比較と終頂点の厳密不等式を使う。
規約：全頂点の比較を結論にする。使われ方：Riehl–Verity §4.1の切れ目の実分解。 -/
lemma WalkingAdjunctionPlusCut.le_target (a : WalkingAdjunctionPlusCut H)
    (hr : Y = .minus → (a.value (Fin.last n)).val <
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n))) :
    ∀ i, walkingAdjunctionCutRank (M := .plus) a i ≤
      walkingAdjunctionCutRank (walkingAdjunctionTargetCut H) i := by
  cases Y
  · intro i
    have hc := walkingAdjunctionTargetCut_rank_card H i
    have hi := (a.value i).isLt
    change 2 * (a.value i).val + 0 ≤ _
    simp only [walkingAdjunctionTargetCorrection] at hc
    omega
  · have hp := hr rfl
    rcases walkingAdjunctionCutRank_total (M := .plus) (N := .minus) a
        (walkingAdjunctionTargetCut H) with h | h
    · exact h
    · exfalso
      have hi := h (Fin.last n)
      have hc := walkingAdjunctionTargetCut_rank_card H (Fin.last n)
      change _ ≤ 2 * (a.value (Fin.last n)).val + 0 at hi
      simp only [walkingAdjunctionTargetCorrection] at hc
      omega

end SerrePositivity.InfinityCategories.HA.Monads

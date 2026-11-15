module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutBounds

/-!
概要：端点の指定された値を持つ切れ目を左右の外端の実切れ目と照合する。
方針：plusの切れ目は終頂点、minusの共有点は始頂点の値で区別する。
規約：自然性も含む切れ目の実データの等式を得る。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の境界。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：始点plusの終頂点で値0の切れ目は左外端。
方針：終頂点での単射性と左外端の座標0を使う。規約：全データの等式。
使われ方：Riehl–Verity §4.1の原子の左境界。 -/
lemma WalkingAdjunctionPlusCut.eq_source_of_last_zero {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom .plus Y} (a : WalkingAdjunctionPlusCut H)
    (hz : (a.value (Fin.last n)).val = 0) : a = walkingAdjunctionSourceCut H := by
  apply WalkingAdjunctionPlusCut.last_injective
  apply Fin.ext
  change (a.value (Fin.last n)).val =
    walkingAdjunctionCutCoordinate (walkingAdjunctionSourceCut H) (Fin.last n)
  rw [walkingAdjunctionSourceCut_coordinate]
  exact hz

/-- 概要：終点plusの終頂点で最外端の値を持つ切れ目は右外端。
方針：終頂点での単射性と右外端の座標を使う。規約：全データの等式。
使われ方：Riehl–Verity §4.1の原子の右境界。 -/
lemma WalkingAdjunctionPlusCut.eq_target_of_last_card {n : ℕ} {X : WalkingAdjunctionPoint}
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom X .plus} (a : WalkingAdjunctionPlusCut H)
    (ht : (a.value (Fin.last n)).val =
      walkingAdjunctionOrdinalCard X .plus (H.obj (Fin.last n))) :
    a = walkingAdjunctionTargetCut H := by
  apply WalkingAdjunctionPlusCut.last_injective
  apply Fin.ext
  change (a.value (Fin.last n)).val =
    walkingAdjunctionCutCoordinate (walkingAdjunctionTargetCut H) (Fin.last n)
  rw [walkingAdjunctionTargetCut_coordinate]
  have hc := walkingAdjunctionOrdinalCard_weight X .plus (H.obj (Fin.last n))
  change walkingAdjunctionOrdinalCard X .plus (H.obj (Fin.last n)) =
    walkingAdjunctionWeight X .plus (H.obj (Fin.last n)) + 0 at hc
  omega

/-- 概要：始点minusの始頂点で値0の共有点は左外端。
方針：始頂点での単射性と左外端の座標0を使う。規約：全データの等式。
使われ方：Riehl–Verity §4.1の原子の左境界。 -/
lemma WalkingAdjunctionMinusCut.eq_source_of_first_zero {n : ℕ} {Y : WalkingAdjunctionPoint}
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom .minus Y} (a : WalkingAdjunctionMinusCut H)
    (hz : (a.value 0).val = 0) : a = walkingAdjunctionSourceCut H := by
  apply WalkingAdjunctionMinusCut.first_injective
  apply Fin.ext
  change (a.value 0).val = walkingAdjunctionCutCoordinate (walkingAdjunctionSourceCut H) 0
  rw [walkingAdjunctionSourceCut_coordinate]
  exact hz

/-- 概要：終点minusの始頂点で最後の値を持つ共有点は右外端。
方針：始頂点での単射性と右外端の座標を使う。規約：全データの等式。
使われ方：Riehl–Verity §4.1の原子の右境界。 -/
lemma WalkingAdjunctionMinusCut.eq_target_of_first_top {n : ℕ} {X : WalkingAdjunctionPoint}
    {H : Fin (n + 1) ⥤ walkingAdjunctionHom X .minus} (a : WalkingAdjunctionMinusCut H)
    (ht : (a.value 0).val + 1 = walkingAdjunctionOrdinalCard X .minus (H.obj 0)) :
    a = walkingAdjunctionTargetCut H := by
  apply WalkingAdjunctionMinusCut.first_injective
  apply Fin.ext
  change (a.value 0).val = walkingAdjunctionCutCoordinate (walkingAdjunctionTargetCut H) 0
  rw [walkingAdjunctionTargetCut_coordinate]
  have hc := walkingAdjunctionOrdinalCard_weight X .minus (H.obj 0)
  change walkingAdjunctionOrdinalCard X .minus (H.obj 0) =
    walkingAdjunctionWeight X .minus (H.obj 0) + 1 at hc
  omega

end SerrePositivity.InfinityCategories.HA.Monads

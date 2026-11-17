module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOuterCuts
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutInclusions

/-!
概要：左右の外端の間の実区間関手は元の全単体そのもの。
方針：対象は重み、射は実包含の正方形とその値で照合する。
規約：対象だけでなく全ての射を含む関手の等式を得る。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の元の単体との比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：左右の外端の区間の対象は元の全単体の対象。
方針：座標差と元の重みを比較する。規約：全頂点。
使われ方：Riehl–Verity §4.1の全区間の回収。 -/
lemma walkingAdjunctionWholeInterval_obj {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (i : Fin (n + 1)) :
    (walkingAdjunctionCutIntervalFunctor (walkingAdjunctionSourceCut H)
      (walkingAdjunctionTargetCut H) (walkingAdjunctionOuterCuts_le H)).obj i = H.obj i := by
  apply walkingAdjunctionWeight_injective X Y
  change walkingAdjunctionWeight X Y
    (walkingAdjunctionCutIntervalObject (walkingAdjunctionSourceCut H)
      (walkingAdjunctionTargetCut H) (walkingAdjunctionOuterCuts_le H) i) = _
  rw [walkingAdjunctionCutIntervalObject_weight, walkingAdjunctionSourceCut_coordinate,
    walkingAdjunctionTargetCut_coordinate, Nat.sub_zero]

/-- 概要：左右の外端の区間の実関手は元の全単体に全関手として一致する。
方針：全区間の実包含が各点の値を変えないことを正方形に適用する。
規約：全射の照合であり同型の存在を仮定しない。使われ方：Riehl–Verity §4.1。 -/
lemma walkingAdjunctionWholeInterval {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) :
    walkingAdjunctionCutIntervalFunctor (walkingAdjunctionSourceCut H)
      (walkingAdjunctionTargetCut H) (walkingAdjunctionOuterCuts_le H) = H := by
  refine CategoryTheory.Functor.hext (walkingAdjunctionWholeInterval_obj H) ?_
  intro i j f
  apply walkingAdjunctionOrderHom_hext (walkingAdjunctionWholeInterval_obj H i)
    (walkingAdjunctionWholeInterval_obj H j)
  apply ordinalHom_hext
    (congrArg (walkingAdjunctionOrdinalCard X Y) (walkingAdjunctionWholeInterval_obj H i))
    (congrArg (walkingAdjunctionOrdinalCard X Y) (walkingAdjunctionWholeInterval_obj H j))
  intro k l hkl
  have he : walkingAdjunctionCutFunctorInclusion (walkingAdjunctionSourceCut H)
      (walkingAdjunctionTargetCut H) (walkingAdjunctionOuterCuts_le H) i k = l := by
    apply Fin.ext
    rw [walkingAdjunctionCutFunctorInclusion_val, walkingAdjunctionSourceCut_coordinate,
      Nat.zero_add]
    exact hkl
  have hs := congrArg Fin.val (congrArg (fun q => q k)
    (walkingAdjunctionCutFunctor_square (walkingAdjunctionSourceCut H)
      (walkingAdjunctionTargetCut H) (walkingAdjunctionOuterCuts_le H) f))
  change (walkingAdjunctionCutFunctorInclusion (walkingAdjunctionSourceCut H)
      (walkingAdjunctionTargetCut H) (walkingAdjunctionOuterCuts_le H) j
        (walkingAdjunctionOrderHom
          ((walkingAdjunctionCutIntervalFunctor (walkingAdjunctionSourceCut H)
            (walkingAdjunctionTargetCut H) (walkingAdjunctionOuterCuts_le H)).map f) k)).val =
    (walkingAdjunctionOrderHom (H.map f)
      (walkingAdjunctionCutFunctorInclusion (walkingAdjunctionSourceCut H)
        (walkingAdjunctionTargetCut H) (walkingAdjunctionOuterCuts_le H) i k)).val at hs
  rw [walkingAdjunctionCutFunctorInclusion_val, walkingAdjunctionSourceCut_coordinate,
    Nat.zero_add, he] at hs
  exact hs

end SerrePositivity.InfinityCategories.HA.Monads

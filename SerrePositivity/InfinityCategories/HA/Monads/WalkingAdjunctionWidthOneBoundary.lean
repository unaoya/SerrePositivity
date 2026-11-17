module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionWidthOneGenerator
public import
  SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPrefixBoundaryRecognition
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstFaceWidth

/-!
概要：幅1の実因子が前置された境界面は、元の最初の併合がその境界にある場合に限られる。
方針：幅1の因子を実生成射へ戻し、最後では実親の一意性、先頭では実辺の同型性を使う。
規約：幅の等しい親が現れる例外の実全関手を識別する。
使われ方：Riehl–Verity Proposition 4.2.15の境界因子の親、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの例外の除去。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：幅1の実因子を前置した最後の面は、元の実親と最後の実最初の位置を回収する。
方針：前置因子を実生成射の定値関手へ戻し、実境界面の実親の識別を使う。
規約：前置因子や原子の非退化性を入力にしない。使われ方：Riehl–Verity §4.2の最後の例外。 -/
lemma walkingAdjunctionLastFace_widthOne_prefix_control {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (Q : ComposableArrows (walkingAdjunctionHom .minus .plus) n)
    (E : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) E)
    (hq : walkingAdjunctionOrdinalWidth Q = 1)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hface : finiteChainFace H (Fin.last (n + 1)) =
      Q.prod' E ⋙ walkingAdjunctionHorizontal .minus .plus Y) :
    H = walkingAdjunctionPlusParent E ha ∧
      walkingAdjunctionFirstBottomMergeIndex H hlast hnd = Fin.last n := by
  have hq' := walkingAdjunctionWidthOne_minus_plus_generator Q hq
  have he : finiteChainFace H (Fin.last (n + 1)) = walkingAdjunctionPlusParentPrefix E := by
    simpa only [hq', walkingAdjunctionPlusParentPrefix] using hface
  exact ⟨walkingAdjunction_eq_plusParent_of_last_face_prefix H E ha hlast he,
    walkingAdjunctionFirstIndex_last_of_last_face_prefix H E hlast hnd he⟩

/-- 概要：幅1の実因子と実原子の合成が先頭面なら、元の最初の実併合は先頭にある。
方針：先頭でないと仮定し、先頭面の幅の保存と同じ実始点の個数から先頭辺を同型に戻す。
規約：元の実非退化性と最小元の等式を保持。使われ方：Riehl–Verity §4.2の先頭の例外。 -/
lemma walkingAdjunctionFirstIndex_zero_of_first_face_widthOne_prefix {n : ℕ}
    {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (Q : ComposableArrows (walkingAdjunctionHom .minus .plus) n)
    (E : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hea : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) E)
    (hq : walkingAdjunctionOrdinalWidth Q = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hface : H.δ₀ = Q.prod' E ⋙ walkingAdjunctionHorizontal .minus .plus Y) :
    walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = 0 := by
  by_contra hk
  have hq' := walkingAdjunctionWidthOne_minus_plus_generator Q hq
  have he : H.δ₀ = walkingAdjunctionPlusParentPrefix E := by
    simpa only [hq', walkingAdjunctionPlusParentPrefix] using hface
  have hw := (walkingAdjunctionFirstFace_width_and_not_atomic H ha hnd hk).1
  have h0 := (walkingAdjunctionAtomic_endpoint_cards H ha).1
  have hE := (walkingAdjunctionAtomic_endpoint_cards E hea).1
  have h1 := congrArg (walkingAdjunctionOrdinalCard .minus Y)
    (CategoryTheory.Functor.congr_obj he 0)
  rw [walkingAdjunctionPlusParentPrefix_card] at h1
  change walkingAdjunctionOrdinalCard .minus Y (H.obj 1) =
    1 + walkingAdjunctionOrdinalCard .plus Y (E.obj 0) at h1
  have hc : walkingAdjunctionOrdinalCard .minus Y (H.obj 0) =
      walkingAdjunctionOrdinalCard .minus Y (H.obj 1) := by
    change walkingAdjunctionOrdinalCard .minus Y (H.obj 0) =
      1 + walkingAdjunctionTargetCorrection Y at h0
    change walkingAdjunctionOrdinalCard .plus Y (E.obj 0) =
      0 + walkingAdjunctionTargetCorrection Y at hE
    omega
  have hd := walkingAdjunctionOrdinalWidth_first_face_defect H
  rw [hw] at hd
  have hl := ordinalImageCard_le_source (walkingAdjunctionOrderHom (H.map' 0 1))
  have hr : ordinalImageCard (walkingAdjunctionOrderHom (H.map' 0 1)) =
      walkingAdjunctionOrdinalCard .minus Y (H.obj 0) := by
    change ordinalImageCard (walkingAdjunctionOrderHom (H.map' 0 1)) ≤
      walkingAdjunctionOrdinalCard .minus Y (H.obj 0) at hl
    omega
  have hv : ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1)) = 0 := by
    unfold ordinalMapVariation
    rw [hr]
    change walkingAdjunctionOrdinalCard .minus Y (H.obj 0) +
      walkingAdjunctionOrdinalCard .minus Y (H.obj 1) -
      2 * walkingAdjunctionOrdinalCard .minus Y (H.obj 0) = 0
    omega
  exact ((walkingAdjunctionHomShape_nondegenerate_iff_no_isIso H).mp hnd 0)
    ((walkingAdjunctionMapVariation_zero_iff_isIso _).mp hv)

end SerrePositivity.InfinityCategories.HA.Monads

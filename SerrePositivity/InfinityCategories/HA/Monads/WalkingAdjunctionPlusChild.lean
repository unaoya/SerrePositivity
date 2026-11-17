module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionLastFaceData
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionLastParentUniqueness

/-!
概要：最初の実併合が純粋な最後の辺である実親から、始点plusの非退化な原子を回収する。
方針：最後の面の一点の前置を除き、実個数と全実辺で原子性・非退化性を検収する。
規約：元の親への再構成の等式を全実関手として示す。
使われ方：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の対応。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：純粋な最初の実併合が最後にある実親から、始点plusの実全単体を回収する。
方針：最後の面の条件を実最小元と純粋性から供給し、一点の前置を取り除く。
規約：子の実関手の存在を入力にしない。使われ方：Riehl–Verity Lemma 4.1.4の逆。 -/
def walkingAdjunctionPlusChild {n : ℕ} {Y : WalkingAdjunctionPoint}
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
    ComposableArrows (walkingAdjunctionHom .plus Y) n :=
  walkingAdjunctionRemoveBottomPrefix (finiteChainFace P (Fin.last (n + 1)))
    (walkingAdjunctionLastFace_no_one_of_first_last P ha hnd hidx)
    (walkingAdjunctionLastFace_card_two_of_first_last_pure P ha hnd hidx hp)

/-- 概要：回収した子へ生成射を前置すると元の実親の最後の面。
方針：一点の前置を除く実構成の全合成則を適用する。
規約：全実関手の等式。使われ方：Riehl–Verity Lemma 4.1.4の指定面の回収。 -/
lemma walkingAdjunctionPlusChild_prefix {n : ℕ} {Y : WalkingAdjunctionPoint}
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
    walkingAdjunctionPlusParentPrefix (walkingAdjunctionPlusChild P ha hnd hidx hp) =
      finiteChainFace P (Fin.last (n + 1)) :=
  walkingAdjunctionRemoveBottomPrefix_prefix _ _ _

/-- 概要：純粋な最後の実親から回収した子は原子的。
方針：個数の加法則と元の実親の両端の個数を端点判定へ戻す。
規約：子の原子性を新しい入力にしない。使われ方：Riehl–Verity Lemma 4.1.4の実逆。 -/
lemma walkingAdjunctionPlusChild_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
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
    WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionPlusChild P ha hnd hidx hp) := by
  let L := finiteChainFace P (Fin.last (n + 1))
  let hno := walkingAdjunctionLastFace_no_one_of_first_last P ha hnd hidx
  let hc := walkingAdjunctionLastFace_card_two_of_first_last_pure P ha hnd hidx hp
  have hfirst := walkingAdjunctionRemoveBottomPrefix_card L hno hc 0
  have hlast := walkingAdjunctionRemoveBottomPrefix_card L hno hc (Fin.last n)
  have hobj := congrArg (walkingAdjunctionOrdinalCard .minus Y) (finiteChainFace_last_obj P 0)
  have hpf := (walkingAdjunctionAtomic_endpoint_cards P ha).1
  change walkingAdjunctionOrdinalCard .minus Y (P.obj 0) =
    1 + walkingAdjunctionTargetCorrection Y at hpf
  apply walkingAdjunctionAtomic_of_endpoint_cards
  · change walkingAdjunctionOrdinalCard .plus Y
      ((walkingAdjunctionPlusChild P ha hnd hidx hp).obj 0) =
        0 + walkingAdjunctionTargetCorrection Y
    change 1 + walkingAdjunctionOrdinalCard .plus Y
      ((walkingAdjunctionPlusChild P ha hnd hidx hp).obj 0) =
        walkingAdjunctionOrdinalCard .minus Y (L.obj 0) at hfirst
    change walkingAdjunctionOrdinalCard .minus Y (L.obj 0) =
      walkingAdjunctionOrdinalCard .minus Y (P.obj 0) at hobj
    omega
  · have htwo : walkingAdjunctionOrdinalCard .minus Y (L.obj (Fin.last n)) = 2 := hc
    change 1 + walkingAdjunctionOrdinalCard .plus Y
      ((walkingAdjunctionPlusChild P ha hnd hidx hp).obj (Fin.last n)) =
        walkingAdjunctionOrdinalCard .minus Y (L.obj (Fin.last n)) at hlast
    change walkingAdjunctionOrdinalCard .plus Y
      ((walkingAdjunctionPlusChild P ha hnd hidx hp).obj (Fin.last n)) = 1
    have hm : 1 + walkingAdjunctionOrdinalCard .plus Y
        ((walkingAdjunctionPlusChild P ha hnd hidx hp).obj (Fin.last n)) = 2 := hlast.trans htwo
    omega

/-- 概要：純粋な最後の実親から回収した子は元のHomのnerveで非退化。
方針：子の同型辺は前置と最後の面で親の同型辺を与え、親の非退化性に反する。
規約：長さ0を含む全次数。使われ方：Riehl–Verity Lemma 4.1.4の実逆。 -/
lemma walkingAdjunctionPlusChild_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
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
    ULift.up (walkingAdjunctionPlusChild P ha hnd hidx hp) ∈
      (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate n := by
  cases n with
  | zero => rw [SSet.nondegenerate_zero]; trivial
  | succ n =>
    let D := walkingAdjunctionPlusChild P ha hnd hidx hp
    let L := finiteChainFace P (Fin.last (n + 2))
    have he : walkingAdjunctionPlusParentPrefix D = L :=
      walkingAdjunctionPlusChild_prefix P ha hnd hidx hp
    apply (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso D).mpr
    intro j hj
    have := hj
    have hpre : IsIso ((walkingAdjunctionPlusParentPrefix D).map
        (homOfLE (Fin.castSucc_le_succ j))) := by
      change IsIso ((walkingAdjunctionHorizontal .minus .plus Y).map
        (X := (walkingAdjunctionGeneratorVertex .minus, D.obj j.castSucc))
        (Y := (walkingAdjunctionGeneratorVertex .minus, D.obj j.succ))
        (𝟙 (walkingAdjunctionGeneratorVertex .minus),
          D.map (homOfLE (Fin.castSucc_le_succ j))))
      have : IsIso (CategoryTheory.Prod.mkHom (𝟙 (walkingAdjunctionGeneratorVertex .minus))
          (D.map (homOfLE (Fin.castSucc_le_succ j)))) :=
        (inferInstance : IsIso ((Iso.prod (Iso.refl (walkingAdjunctionGeneratorVertex .minus))
          (asIso (D.map (homOfLE (Fin.castSucc_le_succ j))))).hom))
      infer_instance
    have := hpre
    have hl : IsIso (L.map (homOfLE (Fin.castSucc_le_succ j))) :=
      isIso_of_equal_objects_hom_heq (CategoryTheory.Functor.congr_obj he j.castSucc)
        (CategoryTheory.Functor.congr_obj he j.succ) _ _
        (CategoryTheory.Functor.hcongr_hom he (homOfLE (Fin.castSucc_le_succ j)))
    have := hl
    have hpar : IsIso (P.map (homOfLE (Fin.castSucc_le_succ j.castSucc))) :=
      isIso_of_equal_objects_hom_heq (finiteChainFace_last_obj P j.castSucc)
        (finiteChainFace_last_obj P j.succ) _ _ (finiteChainFace_last_edge P j)
    exact (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso P).mp hnd j.castSucc hpar

/-- 概要：回収した始点plusの子から親を実際に再構成すると、元の実親に戻る。
方針：同じ最後の実面と、個数1の実終点による全関手の一意性を使う。
規約：全実関手の往復。使われ方：Riehl–Verity Lemma 4.1.4の実親の対応。 -/
lemma walkingAdjunctionPlusChild_parent {n : ℕ} {Y : WalkingAdjunctionPoint}
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
    walkingAdjunctionPlusParent (walkingAdjunctionPlusChild P ha hnd hidx hp)
      (walkingAdjunctionPlusChild_atomic P ha hnd hidx hp) = P := by
  apply walkingAdjunction_eq_of_last_face_and_card_one
  · exact (walkingAdjunctionPlusParent_face_last _ _).trans
      (walkingAdjunctionPlusChild_prefix P ha hnd hidx hp)
  · exact (walkingAdjunctionAtomic_endpoint_cards _ (walkingAdjunctionPlusParent_atomic _ _)).2
  · exact (walkingAdjunctionAtomic_endpoint_cards P ha).2

end SerrePositivity.InfinityCategories.HA.Monads

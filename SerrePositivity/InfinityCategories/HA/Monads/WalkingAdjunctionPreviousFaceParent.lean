module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPreviousFace
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstRefinementIndex
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthRefinement

/-!
概要：指定直前の非純粋な実面の実親は、元より深さが小さく、幅は元以下となる。
方針：実面の原子性・非退化性・非純粋性から既存の実親を構成し、その幅と実位置を戻す。
規約：親やその幅・深さの証人を入力にせず、元の実鎖と全点の条件から回収する。
使われ方：Riehl–Verity Proposition 4.2.15の指定直前の面の実親、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの順序づけ。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：値1を通る先行辺の指定直前の実面は、幅が元以下で深さが真に小さい実親を持つ。
方針：実面の検収から構成済みの実細分を取り、その幅の保存と最初の実位置を計算する。
規約：元の実最小元で定義した全関手を結論に保持。使われ方：Riehl–Verity §4.2の実親の比較。 -/
lemma walkingAdjunctionPreviousFace_parent_control {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = k.succ)
    (hbc : walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.succ) + 1 =
      walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ.castSucc))
    (hg : ∀ i, (walkingAdjunctionOrderHom
      (H.map (homOfLE (Fin.castSucc_le_succ k.succ))) i).val = i.val - 1)
    (hthrough : ∃ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc.castSucc)),
      i.val = 1 ∧ (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = 1) :
    let F := finiteChainFace H k.succ.castSucc
    let fa := walkingAdjunctionInnerFace_atomic H k ha
    ∃ hf : ULift.up F ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1),
      ∃ hp : ULift.up (walkingAdjunctionFirstRefinement F fa hf) ∈
          (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2),
        walkingAdjunctionOrdinalWidth (walkingAdjunctionFirstRefinement F fa hf) ≤
          walkingAdjunctionOrdinalWidth H ∧
        (walkingAdjunctionFirstBottomMergeIndex (walkingAdjunctionFirstRefinement F fa hf)
          (walkingAdjunctionAtomic_endpoint_cards _
            (walkingAdjunctionFirstRefinement_atomic F fa hf)).2 hp).val <
          (walkingAdjunctionFirstBottomMergeIndex H
            (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd).val := by
  let F := finiteChainFace H k.succ.castSucc
  let fa := walkingAdjunctionInnerFace_atomic H k ha
  obtain ⟨hf, hfi, hnp⟩ := walkingAdjunctionPreviousFace_control H k
    (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd hidx hbc hg hthrough
  have hfi' : walkingAdjunctionFirstBottomMergeIndex F
      (walkingAdjunctionAtomic_endpoint_cards F fa).2 hf = k := hfi
  have hnp' :
      let j := walkingAdjunctionFirstBottomMergeIndex F
        (walkingAdjunctionAtomic_endpoint_cards F fa).2 hf
      let m := walkingAdjunctionOrdinalCard .minus Y (F.obj j.castSucc) - 2
      ¬ (walkingAdjunctionOrdinalCard .minus Y (F.obj j.succ) = m + 1 ∧
        ∀ i, (walkingAdjunctionOrderHom
          (F.map (homOfLE (Fin.castSucc_le_succ j))) i).val = i.val - 1) := by
    dsimp only
    rw [hfi']
    exact hnp
  have hp := walkingAdjunctionFirstRefinement_nondegenerate_of_not_pure F fa hf hnp'
  refine ⟨hf, hp, ?_, ?_⟩
  · rw [walkingAdjunctionFirstRefinement_ordinalWidth]
    exact walkingAdjunctionOrdinalWidth_face_le (n + 1) H k.succ.castSucc
  · rw [walkingAdjunctionFirstRefinement_first_index, hfi', hidx]
    change k.val < k.val + 1
    omega

end SerrePositivity.InfinityCategories.HA.Monads

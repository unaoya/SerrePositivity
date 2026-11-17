module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRefinementFirstMerge

/-!
概要：構成した実最初の細分の最小の併合添字を、元の実最小元そのものへ戻す。
方針：構成済みの実所属・最小性と、新しい有限最小元の所属・最小性を比較する。
規約：非退化性が確認された実細分についての等式。
使われ方：Riehl–Verity Proposition 4.2.15の実親の深さ、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの深さの照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：非退化な実細分の最初の添字は、元の実最初の添字のcastSucc。
方針：二つの実最小性を互いの実所属へ適用する。
規約：添字を新しく選び直さない。使われ方：Riehl–Verity §4.2の実親の深さの保存。 -/
lemma walkingAdjunctionFirstRefinement_first_index {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hp : ULift.up (walkingAdjunctionFirstRefinement H ha hnd) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2)) :
    walkingAdjunctionFirstBottomMergeIndex (walkingAdjunctionFirstRefinement H ha hnd)
      (walkingAdjunctionAtomic_endpoint_cards _
        (walkingAdjunctionFirstRefinement_atomic H ha hnd)).2
      hp = (walkingAdjunctionFirstBottomMergeIndex H
        (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd).castSucc := by
  have hm := walkingAdjunctionFirstRefinement_first_merge H ha hnd
  exact le_antisymm (walkingAdjunctionFirstBottomMergeIndex_minimal _ _ hp hm.1)
    (hm.2 _ (walkingAdjunctionFirstBottomMergeIndex_spec _ _ hp))

end SerrePositivity.InfinityCategories.HA.Monads

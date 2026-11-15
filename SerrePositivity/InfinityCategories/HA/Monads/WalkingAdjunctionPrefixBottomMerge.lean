module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParent
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergePositions
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPrefixInclusions

/-!
概要：実生成射を前置した全鎖の辺では二番目の実点は0へ送られない。
方針：実水平合成の順序和表示で、一点の左区間より右の像が正であることを使う。
規約：退化・原子性の仮定を加えず、全実辺を検収する。
使われ方：Riehl–Verity Lemma 4.1.4の最後の折り返し、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の最初の実併合の位置。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：生成射を前置した実全鎖には最初の二点の併合の辺がない。
方針：個数の等式を移して実順序和の右区間で値を計算する。
規約：元の全隣接実辺。使われ方：Riehl–Verity Lemma 4.1.4の最後の深さ。 -/
lemma walkingAdjunctionPlusParentPrefix_no_bottom_merge {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) (n + 1)) (j : Fin (n + 1)) :
    ¬ WalkingAdjunctionBottomMergeAt (walkingAdjunctionPlusParentPrefix H) j := by
  rintro ⟨i, hi, hz⟩
  let U := walkingAdjunctionGeneratorVertex .minus
  let f := H.map (homOfLE (Fin.castSucc_le_succ j))
  have ha := walkingAdjunctionPlusParentPrefix_card H j.castSucc
  have hb := walkingAdjunctionPlusParentPrefix_card H j.succ
  let i' := Fin.cast ha i
  have he := walkingAdjunctionOrderHom_comp_plus .minus Y (𝟙 U) f
  have hv := ordinalOrderHom_heq_val ha hb _ _ he i i' rfl
  have hp := ordinalAppend_val_right (walkingAdjunctionOrderHom (𝟙 U))
    (walkingAdjunctionOrderHom f) i' (by change 1 ≤ i'.val; exact Nat.le_of_eq hi.symm)
  change (walkingAdjunctionOrderHom
    ((walkingAdjunctionPlusParentPrefix H).map (homOfLE (Fin.castSucc_le_succ j))) i).val = _ at hv
  change (ordinalAppend (walkingAdjunctionOrderHom (𝟙 U)) (walkingAdjunctionOrderHom f) i').val =
    1 + _ at hp
  omega

end SerrePositivity.InfinityCategories.HA.Monads

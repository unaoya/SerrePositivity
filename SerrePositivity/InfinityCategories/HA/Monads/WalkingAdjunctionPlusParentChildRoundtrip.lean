module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusChild

/-!
概要：始点plusの実原子から作った親と回収した子の実全関手の往復を照合する。
方針：最後の純粋な辺の個数の表示を揃え、実前置の単射性で元の全関手へ戻す。
規約：選択した実位置・元のHomの非退化性・原子性の証明は構成済みのものを使う。
使われ方：Riehl–Verity Lemma 4.1.4の実親の対応、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親と実子の検収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：始点plusからの実親の最後の辺の始点は二点。
方針：終端挿入前の実対象の回収と実生成射の前置の個数を合わせる。
規約：実親の対象の個数の等式。使われ方：Riehl–Verity Lemma 4.1.4の純粋性の表示。 -/
lemma walkingAdjunctionPlusParent_before_last_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard .minus Y
      ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).castSucc) = 2 := by
  exact (congrArg (walkingAdjunctionOrdinalCard .minus Y)
    (composableArrowAppend_before_obj (walkingAdjunctionPlusParentPrefix H)
      (walkingAdjunctionBottomMergeObject Y 0)
      (walkingAdjunctionBottomMergeArrow
        ((walkingAdjunctionPlusParentPrefix H).obj (Fin.last n)) 0
        (walkingAdjunctionPlusParentPrefix_last_card H ha)) (Fin.last n))).trans
          (walkingAdjunctionPlusParentPrefix_last_card H ha)

/-- 概要：構成した実親の最後の純粋性を、始点の個数から定まる表示へ戻す。
方針：始点の個数2の等式を終点の個数1の条件へ適用する。
規約：全点の値は元の実辺のまま。使われ方：Riehl–Verity Lemma 4.1.4の逆の入力。 -/
lemma walkingAdjunctionPlusParent_last_pure_with_source {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).succ) =
      walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y
        ((walkingAdjunctionPlusParent H ha).obj (Fin.last n).castSucc)),
        (walkingAdjunctionOrderHom ((walkingAdjunctionPlusParent H ha).map
          (homOfLE (Fin.castSucc_le_succ (Fin.last n)))) i).val = i.val - 1 := by
  refine ⟨?_, (walkingAdjunctionPlusParent_last_pure H ha).2⟩
  rw [walkingAdjunctionPlusParent_before_last_card]
  exact (walkingAdjunctionPlusParent_last_pure H ha).1

/-- 概要：始点plusの非退化な実原子から親を構成し、その子を回収すると元の全実関手。
方針：回収した子の前置と実親の最後の面を照合し、実前置の単射性を使う。
規約：全実関手の往復であり同型類だけに落とさない。使われ方：Riehl–Verity Lemma 4.1.4。 -/
lemma walkingAdjunctionPlusParent_child {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate n) :
    walkingAdjunctionPlusChild (walkingAdjunctionPlusParent H ha)
      (walkingAdjunctionPlusParent_atomic H ha) (walkingAdjunctionPlusParent_nondegenerate H ha hnd)
      (walkingAdjunctionPlusParent_first_index H ha hnd)
      (walkingAdjunctionPlusParent_last_pure_with_source H ha) = H := by
  apply walkingAdjunctionPlusParentPrefix_injective
  exact (walkingAdjunctionPlusChild_prefix _ _ _ _ _).trans
    (walkingAdjunctionPlusParent_face_last H ha)

end SerrePositivity.InfinityCategories.HA.Monads

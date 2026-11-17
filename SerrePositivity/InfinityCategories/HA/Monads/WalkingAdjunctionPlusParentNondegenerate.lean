module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPrefixIsomorphisms

/-!
概要：始点plusの非退化な原子から構成した実親は元のHomのnerveで非退化。
方針：最後の辺は実個数2から1、それ以前は前置した元の実辺へ戻して同型性を否定する。
規約：長さ0も含む元の全次数、親の非退化性は実構成から証明する。
使われ方：Riehl–Verity Lemma 4.1.4の最後の深さの親、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実非退化性の検収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：始点plusの原子から構成した実親は、元が非退化なら非退化。
方針：最後の併合の個数の相違と、それ以前の実辺の回収・同型性の反映を使う。
規約：親の非退化性やその辺の条件を新しい入力にしない。使われ方：Riehl–Verity Lemma 4.1.4。 -/
lemma walkingAdjunctionPlusParent_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate n) :
    ULift.up (walkingAdjunctionPlusParent H ha) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1) := by
  let L := walkingAdjunctionPlusParentPrefix H
  let B := walkingAdjunctionBottomMergeObject Y 0
  let q := walkingAdjunctionBottomMergeArrow (L.obj (Fin.last n)) 0
    (walkingAdjunctionPlusParentPrefix_last_card H ha)
  let P := walkingAdjunctionPlusParent H ha
  apply (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso P).mpr
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · intro hj
    have := hj
    have hc := walkingAdjunctionCard_eq_of_isIso
      (P.map (homOfLE (Fin.castSucc_le_succ (Fin.last n))))
    have hs := congrArg (walkingAdjunctionOrdinalCard .minus Y)
      (composableArrowAppend_before_obj L B q (Fin.last n))
    have ht := congrArg (walkingAdjunctionOrdinalCard .minus Y)
      (composableArrowAppend_last L B q)
    have hl := walkingAdjunctionPlusParentPrefix_last_card H ha
    have hb := walkingAdjunctionBottomMergeObject_card Y 0
    change walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc) =
      walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last (n + 1))) at hc
    change walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last n).castSucc) =
      walkingAdjunctionOrdinalCard .minus Y (L.obj (Fin.last n)) at hs
    change walkingAdjunctionOrdinalCard .minus Y (P.obj (Fin.last (n + 1))) =
      walkingAdjunctionOrdinalCard .minus Y B at ht
    change walkingAdjunctionOrdinalCard .minus Y (L.obj (Fin.last n)) = 2 at hl
    change walkingAdjunctionOrdinalCard .minus Y B = 1 at hb
    omega
  · intro hj
    cases n with
    | zero => exact Fin.elim0 j
    | succ n =>
      have hn := walkingAdjunctionPlusParentPrefix_nondegenerate H hnd
      have hno := (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso L).mp hn j
      apply hno
      have := hj
      have hs : P.obj j.castSucc.castSucc = L.obj j.castSucc :=
        composableArrowAppend_before_obj L B q j.castSucc
      have ht : P.obj j.castSucc.succ = L.obj j.succ :=
        composableArrowAppend_before_obj L B q j.succ
      exact isIso_of_equal_objects_hom_heq hs ht
        (P.map (homOfLE (Fin.castSucc_le_succ j.castSucc)))
        (L.map (homOfLE (Fin.castSucc_le_succ j)))
        (composableArrowAppend_before_edge L B q j)

end SerrePositivity.InfinityCategories.HA.Monads

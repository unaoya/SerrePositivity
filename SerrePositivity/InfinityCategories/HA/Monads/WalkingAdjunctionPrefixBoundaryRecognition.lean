module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionLastParentUniqueness
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParentPositions

/-!
概要：実生成射の前置になっている最後の境界面から、最後の深さの実親を回収する。
方針：一点の実終点で全関手の一意性を使い、先行する全辺の実非併合で最初の位置を戻す。
規約：前置される鎖の非退化性を入力にしない。
使われ方：Riehl–Verity Proposition 4.2.15の境界で親の幅が一致する場合、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親の識別。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：最後の実面が実生成射の前置で実終点が一点なら、元の鎖は対応する実親そのもの。
方針：実親の指定面と終点を回収し、全実関手の一意性を使う。
規約：同型類でなく同じ実全関手。使われ方：Riehl–Verity §4.2の最後の実面の例外の識別。 -/
lemma walkingAdjunction_eq_plusParent_of_last_face_prefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (E : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) E)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hface : finiteChainFace H (Fin.last (n + 1)) = walkingAdjunctionPlusParentPrefix E) :
    H = walkingAdjunctionPlusParent E ha := by
  exact walkingAdjunction_eq_of_last_face_and_card_one H (walkingAdjunctionPlusParent E ha)
    (hface.trans (walkingAdjunctionPlusParent_face_last E ha).symm) hlast
    (walkingAdjunctionAtomic_endpoint_cards _ (walkingAdjunctionPlusParent_atomic E ha)).2

/-- 概要：最後の実面が実生成射の前置であれば、非退化な元の鎖の最初の実併合は最後の辺。
方針：最後より前の実辺を実面と前置の実辺へ戻し、全ての実併合を排除する。
規約：前置される鎖の原子性・非退化性を仮定しない。使われ方：Riehl–Verity §4.2の境界の深さ。 -/
lemma walkingAdjunctionFirstIndex_last_of_last_face_prefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (E : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last (n + 1))) = 1)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hface : finiteChainFace H (Fin.last (n + 1)) = walkingAdjunctionPlusParentPrefix E) :
    walkingAdjunctionFirstBottomMergeIndex H hlast hnd = Fin.last n := by
  have hlast' (k : Fin (n + 1)) (hm : WalkingAdjunctionBottomMergeAt H k) : k = Fin.last n := by
    refine Fin.lastCases (fun _ => rfl) (fun j hj => ?_) k hm
    cases n with
    | zero => exact Fin.elim0 j
    | succ n =>
      have he := walkingAdjunctionMergesBottom_heq (finiteChainFace_last_obj H j.castSucc)
        (finiteChainFace_last_obj H j.succ) _ _ (finiteChainFace_last_edge H j)
      have hjf : WalkingAdjunctionBottomMergeAt (finiteChainFace H (Fin.last (n + 2))) j :=
        he.mpr hj
      rw [hface] at hjf
      exact False.elim (walkingAdjunctionPlusParentPrefix_no_bottom_merge E j hjf)
  exact hlast' _ (walkingAdjunctionFirstBottomMergeIndex_spec H hlast hnd)

end SerrePositivity.InfinityCategories.HA.Monads

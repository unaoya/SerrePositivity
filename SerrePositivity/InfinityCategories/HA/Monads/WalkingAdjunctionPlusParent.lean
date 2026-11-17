module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowAppendPositions
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicEndpoints
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMerge

/-!
概要：始点plusの原子的な実全単体に生成射を前置し、終端の実併合を挿入する。
方針：実水平合成で全鎖を作り、点の個数2から1への実射を終端へ挿入する。
規約：存在を仮定せず元のHomへの全関手と実指定面・原子性を構成する。
使われ方：Riehl–Verity Lemma 4.1.4の最後の深さの親、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の始点plusの実構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：始点plusの全実鎖へminusからの生成射を実水平合成で前置する。
方針：実生成射の定値関手と元の全実鎖の積を取る。
規約：全射も水平合成で送る。使われ方：Riehl–Verity Lemma 4.1.4の指定面。 -/
def walkingAdjunctionPlusParentPrefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n) :
    ComposableArrows (walkingAdjunctionHom .minus Y) n :=
  ((CategoryTheory.Functor.const (Fin (n + 1))).obj
    (walkingAdjunctionGeneratorVertex .minus)).prod' H ⋙ walkingAdjunctionHorizontal .minus .plus Y

/-- 概要：前置した実生成射は各頂点の点の個数を1増やす。
方針：実水平合成の個数の加法則を使う。規約：全ての実頂点。
使われ方：Riehl–Verity Lemma 4.1.4の実親の両端。 -/
lemma walkingAdjunctionPlusParentPrefix_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n) (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard .minus Y ((walkingAdjunctionPlusParentPrefix H).obj i) =
      1 + walkingAdjunctionOrdinalCard .plus Y (H.obj i) := by
  change walkingAdjunctionOrdinalCard .minus Y ((walkingAdjunctionHorizontal .minus .plus Y).obj
    (walkingAdjunctionGeneratorVertex .minus, H.obj i)) = _
  rw [walkingAdjunctionOrdinalCard_comp_plus]
  rfl

/-- 概要：始点plusの原子に前置した実鎖の終点は二つの実点を持つ。
方針：原子の終点の実個数1と生成射の前置の加法則を合わせる。
規約：原子性から個数を得る。使われ方：Riehl–Verity Lemma 4.1.4の終端の実射。 -/
lemma walkingAdjunctionPlusParentPrefix_last_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionOrdinalCard .minus Y
      ((walkingAdjunctionPlusParentPrefix H).obj (Fin.last n)) = 0 + 2 := by
  rw [walkingAdjunctionPlusParentPrefix_card, (walkingAdjunctionAtomic_endpoint_cards H ha).2]

/-- 概要：始点plusの実原子から一つ高次のminus始点の実親を構成する。
方針：生成射を前置し、二点から一点への実併合を終端に挿入する。
規約：全実関手を構成し、非退化性の検収は分離する。使われ方：Riehl–Verity Lemma 4.1.4。 -/
def walkingAdjunctionPlusParent {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1) :=
  composableArrowAppend (walkingAdjunctionPlusParentPrefix H)
    (walkingAdjunctionBottomMergeObject Y 0)
    (walkingAdjunctionBottomMergeArrow ((walkingAdjunctionPlusParentPrefix H).obj (Fin.last n)) 0
      (walkingAdjunctionPlusParentPrefix_last_card H ha))

/-- 概要：始点plusから構成した実親の最後の面は生成射を前置した元の実鎖。
方針：実終端挿入の最後の面を適用する。規約：全実関手の等式。
使われ方：Riehl–Verity Lemma 4.1.4の最後の深さの指定面。 -/
lemma walkingAdjunctionPlusParent_face_last {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    finiteChainFace (walkingAdjunctionPlusParent H ha) (Fin.last (n + 1)) =
      walkingAdjunctionPlusParentPrefix H :=
  composableArrowAppend_face_last n _ _ _

/-- 概要：始点plusから実際に構成した親は原子的。
方針：終端挿入の両端の等式と実個数の端点判定を使う。
規約：原子性を親の新しい入力に置かない。使われ方：Riehl–Verity Lemma 4.1.4の実親。 -/
lemma walkingAdjunctionPlusParent_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionPlusParent H ha) := by
  apply walkingAdjunctionAtomic_of_endpoint_cards
  · have hf := congrArg (walkingAdjunctionOrdinalCard .minus Y)
      (composableArrowAppend_first (walkingAdjunctionPlusParentPrefix H)
        (walkingAdjunctionBottomMergeObject Y 0)
        (walkingAdjunctionBottomMergeArrow
          ((walkingAdjunctionPlusParentPrefix H).obj (Fin.last n)) 0
          (walkingAdjunctionPlusParentPrefix_last_card H ha)))
    have hp := walkingAdjunctionPlusParentPrefix_card H 0
    have hh := (walkingAdjunctionAtomic_endpoint_cards H ha).1
    change walkingAdjunctionOrdinalCard .plus Y (H.obj 0) =
      0 + walkingAdjunctionTargetCorrection Y at hh
    change walkingAdjunctionOrdinalCard .minus Y ((walkingAdjunctionPlusParent H ha).obj 0) =
      1 + walkingAdjunctionTargetCorrection Y
    change walkingAdjunctionOrdinalCard .minus Y
      ((walkingAdjunctionPlusParent H ha).obj 0) = _ at hf
    omega
  · exact (congrArg (walkingAdjunctionOrdinalCard .minus Y)
      (composableArrowAppend_last (walkingAdjunctionPlusParentPrefix H)
        (walkingAdjunctionBottomMergeObject Y 0) _)).trans
          (walkingAdjunctionBottomMergeObject_card Y 0)

end SerrePositivity.InfinityCategories.HA.Monads

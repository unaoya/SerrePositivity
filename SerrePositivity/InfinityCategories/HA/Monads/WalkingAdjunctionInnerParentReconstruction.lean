module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionInnerFaceFirstMerge
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergeRigidity
public import
  SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRefinementNondegenerateIff

/-!
概要：内側の純粋な実併合の親は、その指定面の実細分として全関手に復元される。
方針：実始点の個数と指定面の併合を供給し、純粋な左辺と面による一意性を適用する。
規約：子の指定辺が非純粋であることも親の非退化性から回収する。
使われ方：Riehl–Verity Lemma 4.1.3の実親の逆方向、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実親と子の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：内側の面の指定実辺の始点の個数は元の始点の個数から定まる。
方針：実始点の等式と併合の実証人による二点以上の下限を使う。
規約：実細分の個数の型を供給する。使われ方：Riehl–Verity Lemma 4.1.3の実親の再構成。 -/
lemma walkingAdjunctionInnerFace_source_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hm : WalkingAdjunctionBottomMergeAt P k.castSucc) :
    walkingAdjunctionOrdinalCard .minus Y
      ((finiteChainFace P k.succ.castSucc).obj k.castSucc) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 2 := by
  rw [finiteChainFace_inner_before_obj P k k.castSucc (by exact le_rfl)]
  exact (Nat.sub_add_cancel hm.card_two_le).symm

/-- 概要：内側の純粋な実併合の親は指定面の実細分と全関手で一致する。
方針：元の実左辺の全点条件と指定面からの一意性を、実個数・併合の証人で適用する。
規約：親の存在や右因子を新しく仮定しない。使われ方：Riehl–Verity Lemma 4.1.3の実逆。 -/
lemma walkingAdjunctionInnerFace_refinement {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hm : WalkingAdjunctionBottomMergeAt P k.castSucc)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) :
    P = walkingAdjunctionBottomMergeRefinement (finiteChainFace P k.succ.castSucc) k
      (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2)
      (walkingAdjunctionInnerFace_source_card P k hm)
      (walkingAdjunctionInnerFace_merge P k hm).one_zero := by
  exact walkingAdjunctionBottomMergeRefinement_unique _ _ _ _ _ P rfl hp

/-- 概要：非退化な内側の純粋な実親の指定面では、指定辺は非純粋。
方針：親を実細分へ戻し、実細分の非退化性と非純粋性の必要十分条件を適用する。
規約：元の子の実辺の全点条件を否定。使われ方：Riehl–Verity Lemma 4.1.3の実逆。 -/
lemma walkingAdjunctionInnerFace_not_pure {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (hm : WalkingAdjunctionBottomMergeAt P k.castSucc)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) :
    ¬ (walkingAdjunctionOrdinalCard .minus Y
        ((finiteChainFace P k.succ.castSucc).obj k.succ) =
          walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y
        ((finiteChainFace P k.succ.castSucc).obj k.castSucc)),
        (walkingAdjunctionOrderHom ((finiteChainFace P k.succ.castSucc).map
          (homOfLE (Fin.castSucc_le_succ k))) i).val = i.val - 1) := by
  have he := walkingAdjunctionInnerFace_refinement P k hm hp
  have hn := he ▸ hnd
  exact (walkingAdjunctionBottomMergeRefinement_nondegenerate_iff_not_pure _ k _
    (walkingAdjunctionInnerFace_source_card P k hm)
    (walkingAdjunctionInnerFace_merge P k hm).one_zero
    (walkingAdjunctionInnerFace_nondegenerate P k hnd hm)).mp hn

/-- 概要：最初の内側の純粋な実親の指定面から実最小元で親を作り直すと元の全関手。
方針：子の実最初の位置と個数を同一視し、指定面の実細分の一意性を使う。
規約：全実関手の往復。使われ方：Riehl–Verity Lemma 4.1.3の実親の対応。 -/
lemma walkingAdjunctionInnerFace_firstRefinement {n : ℕ} {Y : WalkingAdjunctionPoint}
    (P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2)) (k : Fin (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) P)
    (hnd : ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2))
    (hidx : walkingAdjunctionFirstBottomMergeIndex P
      (walkingAdjunctionAtomic_endpoint_cards P ha).2 hnd = k.castSucc)
    (hp : walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) :
    walkingAdjunctionFirstRefinement (finiteChainFace P k.succ.castSucc)
      (walkingAdjunctionInnerFace_atomic P k ha)
      (walkingAdjunctionInnerFace_nondegenerate P k hnd
        (walkingAdjunctionInnerFace_first_merge P k ha hnd hidx)) = P := by
  have hpos := walkingAdjunctionInnerFace_first_index P k ha hnd hidx
  have hs := finiteChainFace_inner_before_obj P k k.castSucc (by exact le_rfl)
  have hm : walkingAdjunctionOrdinalCard .minus Y
      ((finiteChainFace P k.succ.castSucc).obj k.castSucc) - 2 =
      walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 :=
    congrArg (fun A : walkingAdjunctionHom .minus Y =>
      walkingAdjunctionOrdinalCard .minus Y A - 2) hs
  have he := (walkingAdjunctionInnerFace_refinement P k
    (walkingAdjunctionInnerFace_first_merge P k ha hnd hidx) hp).symm
  unfold walkingAdjunctionFirstRefinement
  simp only [hpos, hm]
  exact he

end SerrePositivity.InfinityCategories.HA.Monads

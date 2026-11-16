module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstRefinementIndex
public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowInnerFace
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParentChildRoundtrip

/-!
概要：非退化な実原子の生成元をまとめ、有限順序模型の純粋性の条件と実親を一つの型で保持する。
方針：全実関手・実原子性・元の非退化性を包み、構成済みの二つの実親を場合分けで使う。
規約：NativeFillableはこの有限順序模型の条件。原典の文字列との全比較は別に検収する。
使われ方：Riehl–Verity Definition 4.1.1・4.2.1、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの生成元の型。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：元の全実関手を持つ非退化な実原子の生成元。
方針：元の射・原子性・単体集合での非退化性を保持する。
規約：次数と両端を型に置く。使われ方：Riehl–Verity Definition 4.1.1の生成元の実表示。 -/
structure WalkingAdjunctionAtomicCell (n : ℕ) (X Y : WalkingAdjunctionPoint) where
  chain : ComposableArrows (walkingAdjunctionHom X Y) n
  atomic : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) chain
  nondegenerate : ULift.up chain ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate n

/-- 概要：有限順序模型で、最初の実併合が純粋である生成元の条件。
方針：minus始点の次数0を含め、正の次数では元の実最小元で純粋性を検査する。
規約：原典の文字列の条件との全比較は未完。使われ方：Riehl–Verity Definition 4.1.1。 -/
def WalkingAdjunctionAtomicCell.NativeFillable {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) : Prop :=
  match X, n, a with
  | .plus, _, _ => False
  | .minus, 0, _ => True
  | .minus, _n + 1, a =>
    let k := walkingAdjunctionFirstBottomMergeIndex a.chain
      (walkingAdjunctionAtomic_endpoint_cards a.chain a.atomic).2 a.nondegenerate
    walkingAdjunctionOrdinalCard .minus Y (a.chain.obj k.succ) =
        walkingAdjunctionOrdinalCard .minus Y (a.chain.obj k.castSucc) - 2 + 1 ∧
      ∀ i, (walkingAdjunctionOrderHom
        (a.chain.map (homOfLE (Fin.castSucc_le_succ k))) i).val = i.val - 1

/-- 概要：有限順序模型の非純粋な生成元から、一つ高次の実親を構成する。
方針：plus始点には実終端の親、minus始点には実最初の細分を使い、非退化性を回収する。
規約：実親の存在や非退化性を引数に置かない。使われ方：Riehl–Verity Definition 4.2.1。 -/
def WalkingAdjunctionAtomicCell.parent {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    WalkingAdjunctionAtomicCell.{u} (n + 1) .minus Y := by
  cases X with
  | plus =>
    exact ⟨walkingAdjunctionPlusParent a.chain a.atomic,
      walkingAdjunctionPlusParent_atomic a.chain a.atomic,
      walkingAdjunctionPlusParent_nondegenerate a.chain a.atomic a.nondegenerate⟩
  | minus =>
    cases n with
    | zero => exact False.elim (hnf trivial)
    | succ n =>
      exact ⟨walkingAdjunctionFirstRefinement a.chain a.atomic a.nondegenerate,
        walkingAdjunctionFirstRefinement_atomic a.chain a.atomic a.nondegenerate,
        walkingAdjunctionFirstRefinement_nondegenerate_of_not_pure
          a.chain a.atomic a.nondegenerate hnf⟩

/-- 概要：構成した実親は有限順序模型の純粋性の条件を満たす。
方針：実親の実最小元を回収し、挿入した実辺の個数と全点の値の法則を適用する。
規約：純粋性を親の新しい入力にしない。使われ方：Riehl–Verity Definition 4.2.1の実親。 -/
lemma WalkingAdjunctionAtomicCell.parent_nativeFillable {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (a : WalkingAdjunctionAtomicCell.{u} n X Y) (hnf : ¬ a.NativeFillable) :
    (a.parent hnf).NativeFillable := by
  cases X with
  | plus =>
    change
      let k := walkingAdjunctionFirstBottomMergeIndex (walkingAdjunctionPlusParent a.chain a.atomic)
        (walkingAdjunctionAtomic_endpoint_cards _
          (walkingAdjunctionPlusParent_atomic a.chain a.atomic)).2
        (walkingAdjunctionPlusParent_nondegenerate a.chain a.atomic a.nondegenerate)
      walkingAdjunctionOrdinalCard .minus Y
          ((walkingAdjunctionPlusParent a.chain a.atomic).obj k.succ) =
        walkingAdjunctionOrdinalCard .minus Y
          ((walkingAdjunctionPlusParent a.chain a.atomic).obj k.castSucc) - 2 + 1 ∧
        ∀ i, (walkingAdjunctionOrderHom ((walkingAdjunctionPlusParent a.chain a.atomic).map
          (homOfLE (Fin.castSucc_le_succ k))) i).val = i.val - 1
    dsimp only
    rw [walkingAdjunctionPlusParent_first_index a.chain a.atomic a.nondegenerate]
    exact walkingAdjunctionPlusParent_last_pure_with_source a.chain a.atomic
  | minus =>
    cases n with
    | zero => exact False.elim (hnf trivial)
    | succ n =>
      let H := a.chain
      let k := walkingAdjunctionFirstBottomMergeIndex H
        (walkingAdjunctionAtomic_endpoint_cards H a.atomic).2 a.nondegenerate
      let P := walkingAdjunctionFirstRefinement H a.atomic a.nondegenerate
      have hp := walkingAdjunctionFirstRefinement_nondegenerate_of_not_pure
        H a.atomic a.nondegenerate hnf
      change
        let j := walkingAdjunctionFirstBottomMergeIndex P
          (walkingAdjunctionAtomic_endpoint_cards _
            (walkingAdjunctionFirstRefinement_atomic H a.atomic a.nondegenerate)).2 hp
        walkingAdjunctionOrdinalCard .minus Y (P.obj j.succ) =
            walkingAdjunctionOrdinalCard .minus Y (P.obj j.castSucc) - 2 + 1 ∧
          ∀ i, (walkingAdjunctionOrderHom (P.map
            (homOfLE (Fin.castSucc_le_succ j))) i).val = i.val - 1
      dsimp only
      rw [walkingAdjunctionFirstRefinement_first_index H a.atomic a.nondegenerate hp]
      have hleft := finiteChainFace_inner_before_obj P k k.castSucc le_rfl
      have hface := CategoryTheory.Functor.congr_obj
        (walkingAdjunctionFirstRefinement_face H a.atomic a.nondegenerate) k.castSucc
      have hs : P.obj k.castSucc.castSucc = H.obj k.castSucc := hleft.symm.trans hface
      have hc := congrArg (walkingAdjunctionOrdinalCard .minus Y) hs
      have hpure := walkingAdjunctionFirstRefinement_pure H a.atomic a.nondegenerate
      refine ⟨?_, hpure.2⟩
      have h := hpure.1
      change walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) =
        walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) - 2 + 1 at h
      change walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) =
        walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc) - 2 + 1
      omega

end SerrePositivity.InfinityCategories.HA.Monads

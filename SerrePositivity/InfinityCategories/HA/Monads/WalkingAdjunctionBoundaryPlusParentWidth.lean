module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusFactorParentWidth
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionWidthOneBoundary
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthFaces

/-!
概要：指定面以外の実境界面の始点plusの全原子因子について、実親の幅も元より小さい。
方針：実生成射を前置した例外を元の最初の実位置で排除し、実親の幅の厳密な境界を使う。
規約：親の幅が1増える場合も元の全実道の任意の因子を扱う。
使われ方：Riehl–Verity Proposition 4.2.15の境界因子の親、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの実幅の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：最初の併合が最後でなければ、最後の実面の始点plusの任意の因子の実親は幅が小さい。
方針：実生成射の前置の例外を最後の実最小元の識別で排除する。
規約：全実因子分解とその実親。使われ方：Riehl–Verity §4.2の最後の境界の実親。 -/
lemma walkingAdjunctionLastFace_plusFactor_parent_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ Fin.last n)
    {C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟨⟨.plus⟩⟩)
    (e : (⟨⟨.plus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) =
      finiteChainFace H (Fin.last (n + 1))) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent e.val e.property) <
      walkingAdjunctionOrdinalWidth H := by
  have h := walkingAdjunctionPlusFactor_parent_width_lt _ q e r hfac (by
    intro E _ he
    exact hk (walkingAdjunctionFirstIndex_last_of_last_face_prefix H E
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd he))
  exact lt_of_lt_of_le h (walkingAdjunctionOrdinalWidth_face_le n H (Fin.last (n + 1)))

/-- 概要：最初の併合が先頭でなければ、先頭の実面の始点plusの任意の因子の実親は幅が小さい。
方針：幅1の実生成射の前置の例外を、元の実最小元0の識別で排除する。
規約：前後の実道を空に限定しない。使われ方：Riehl–Verity §4.2の先頭の境界の実親。 -/
lemma walkingAdjunctionFirstFace_plusFactor_parent_width_lt {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ 0)
    {C : WalkingAdjunctionAtomicVertex n}
    (q : Quiver.Path (⟨⟨.minus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟨⟨.plus⟩⟩)
    (e : (⟨⟨.plus⟩⟩ : WalkingAdjunctionAtomicVertex n) ⟶ C)
    (r : Quiver.Path C (⟨⟨Y⟩⟩ : WalkingAdjunctionAtomicVertex n))
    (hfac : (walkingAdjunctionAtomicPathFunctor n).map (q.comp (e.toPath.comp r)) = H.δ₀) :
    walkingAdjunctionOrdinalWidth (walkingAdjunctionPlusParent e.val e.property) <
      walkingAdjunctionOrdinalWidth H := by
  have h := walkingAdjunctionPlusFactor_parent_width_lt _ q e r hfac (by
    intro E hea he
    let Q := (Functor.const (Fin (n + 1))).obj (walkingAdjunctionGeneratorVertex .minus)
    have hq : walkingAdjunctionOrdinalWidth Q = 1 := by
      simp only [Q, walkingAdjunctionOrdinalWidth, Functor.const_obj_obj, Functor.const_obj_map,
        walkingAdjunctionOrderHom_id, ordinalMapVariation_id, Finset.sum_const_zero, Nat.add_zero]
      rfl
    exact hk (walkingAdjunctionFirstIndex_zero_of_first_face_widthOne_prefix H Q E ha hea
      hq hnd he))
  exact lt_of_lt_of_le h (walkingAdjunctionOrdinalWidth_tail_le H)

end SerrePositivity.InfinityCategories.HA.Monads

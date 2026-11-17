module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOnePointSource
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstBottomMerge

/-!
概要：最初の純粋な実併合が先頭なら、次数1のminus自己Homで先頭面は実単位となる。
方針：実原子の始点の個数と併合の実点で終点側の符号を決め、一点からの実鎖を回収する。
規約：元の実最小元と実個数の条件から次数と境界を結論にする。
使われ方：Riehl–Verity Proposition 4.2.15の余単位の場合、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の先頭の実境界面の検収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：始点minusの実原子で最初の併合が先頭なら、終点側もminus。
方針：併合の二番目の実点は始点に二点以上を要求するので、実原子の初期個数を使う。
規約：元の実選択の添字0。使われ方：Riehl–Verity §4.2の先頭の純粋な実親の符号。 -/
lemma walkingAdjunctionTarget_minus_of_first_index_zero {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = 0) : Y = .minus := by
  have hm := walkingAdjunctionFirstBottomMergeIndex_spec H
    (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd
  rw [hk] at hm
  obtain ⟨i, hi, _⟩ := hm
  have hc := (walkingAdjunctionAtomic_endpoint_cards H ha).1
  cases Y with
  | minus => rfl
  | plus =>
    have hlt := i.isLt
    change i.val < walkingAdjunctionOrdinalCard .minus .plus (H.obj 0) at hlt
    change walkingAdjunctionOrdinalCard .minus .plus (H.obj 0) = 1 + 0 at hc
    omega

/-- 概要：先頭の純粋な実併合は、minus自己Homの次数1で、先頭の実面は長さ0の単位。
方針：先頭の個数2と純粋な併合から次の個数1を得て、実単位の回収と非退化性を使う。
規約：元の次数・終点符号・先頭の実面の長さを結論にする。使われ方：Riehl–Verity §4.2。 -/
lemma walkingAdjunctionInitialPureBoundary_control {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd = 0)
    (hp : walkingAdjunctionOrdinalCard .minus Y (H.obj 1) =
      walkingAdjunctionOrdinalCard .minus Y (H.obj 0) - 2 + 1) :
    Y = .minus ∧ n = 0 ∧ walkingAdjunctionLevelSize H.δ₀ = 0 := by
  have hY := walkingAdjunctionTarget_minus_of_first_index_zero H ha hnd hk
  subst Y
  have h0 := (walkingAdjunctionAtomic_endpoint_cards H ha).1
  have hc : walkingAdjunctionOrdinalCard .minus .minus (H.obj 1) = 1 := by
    change walkingAdjunctionOrdinalCard .minus .minus (H.obj 0) = 1 + 1 at h0
    omega
  have htail := walkingAdjunctionMinusChain_eq_identity_of_first_card_one H.δ₀ hc
  refine ⟨rfl, walkingAdjunctionMinusChain_dimension_zero_of_second_card_one H hnd hc, ?_⟩
  rw [htail]
  exact walkingAdjunctionLevelSize_id n .minus

end SerrePositivity.InfinityCategories.HA.Monads

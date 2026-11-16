module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalSmallSourceInjective
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthPrecomp
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstBottomMerge

/-!
概要：先頭面の幅の欠損を始点と実像から計算し、最初の併合より前では幅の保存を示す。
方針：小さい実始点と非併合から単射性を得て、面の非原子性を元の非退化性で回収する。
規約：幅の減少を要求せず、元の実幅と実面の原子性を検収する。
使われ方：Riehl–Verity Proposition 4.2.15の先頭の実境界面、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの実幅の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：先頭面で失う幅は、先頭の実辺の始点と実像の個数の差の二倍。
方針：実先頭挿入の幅の等式に、変化量の定義と像の個数の上限を適用する。
規約：全四Hom・全実鎖。使われ方：Riehl–Verity §4.2の実先頭面の幅の欠損。 -/
lemma walkingAdjunctionOrdinalWidth_first_face_defect {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) :
    walkingAdjunctionOrdinalWidth H = walkingAdjunctionOrdinalWidth H.δ₀ +
      2 * (walkingAdjunctionOrdinalCard X Y (H.obj 0) -
        ordinalImageCard (walkingAdjunctionOrderHom (H.map' 0 1))) := by
  have hw := walkingAdjunctionOrdinalWidth_precomp H.δ₀ (H.map' 0 1)
  rw [composableArrowPrecomp_decompose] at hw
  change walkingAdjunctionOrdinalWidth H + walkingAdjunctionOrdinalCard X Y (H.obj 1) =
    walkingAdjunctionOrdinalWidth H.δ₀ + walkingAdjunctionOrdinalCard X Y (H.obj 0) +
      ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1)) at hw
  have hs := ordinalImageCard_le_source (walkingAdjunctionOrderHom (H.map' 0 1))
  have ht := ordinalImageCard_le_target (walkingAdjunctionOrderHom (H.map' 0 1))
  let r := ordinalImageCard (walkingAdjunctionOrderHom (H.map' 0 1))
  unfold ordinalMapVariation at hw
  change walkingAdjunctionOrdinalWidth H + walkingAdjunctionOrdinalCard X Y (H.obj 1) =
    walkingAdjunctionOrdinalWidth H.δ₀ + walkingAdjunctionOrdinalCard X Y (H.obj 0) +
      (walkingAdjunctionOrdinalCard X Y (H.obj 0) +
        walkingAdjunctionOrdinalCard X Y (H.obj 1) - 2 * r) at hw
  change r ≤ walkingAdjunctionOrdinalCard X Y (H.obj 0) at hs
  change r ≤ walkingAdjunctionOrdinalCard X Y (H.obj 1) at ht
  change walkingAdjunctionOrdinalWidth H = walkingAdjunctionOrdinalWidth H.δ₀ +
    2 * (walkingAdjunctionOrdinalCard X Y (H.obj 0) - r)
  omega

/-- 概要：先頭の実辺が単射なら、先頭面は有限順序の幅を保つ。
方針：実像の個数を始点へ戻し、先頭面の幅の欠損の式を使う。
規約：全実鎖・全四Hom。使われ方：Riehl–Verity §4.2の境界面の幅の等式。 -/
lemma walkingAdjunctionOrdinalWidth_first_face_of_injective {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1))
    (hf : Function.Injective (walkingAdjunctionOrderHom (H.map' 0 1))) :
    walkingAdjunctionOrdinalWidth H.δ₀ = walkingAdjunctionOrdinalWidth H := by
  have hw := walkingAdjunctionOrdinalWidth_first_face_defect H
  have hr := (ordinalImageCard_eq_source_iff (walkingAdjunctionOrderHom (H.map' 0 1))).mpr hf
  change ordinalImageCard (walkingAdjunctionOrderHom (H.map' 0 1)) =
    walkingAdjunctionOrdinalCard X Y (H.obj 0) at hr
  simp only [hr, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hw
  exact hw.symm

/-- 概要：最初の併合が先頭でない非退化な実原子の先頭面は、幅を保ち原子的ではない。
方針：元の最小性で先頭辺の非併合を得て、小さい始点から単射性を示す。
規約：面の幅と原子性を仮定しない。使われ方：Riehl–Verity §4.2の先頭の実境界面。 -/
lemma walkingAdjunctionFirstFace_width_and_not_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1))
    (hk : walkingAdjunctionFirstBottomMergeIndex H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd ≠ 0) :
    walkingAdjunctionOrdinalWidth H.δ₀ = walkingAdjunctionOrdinalWidth H ∧
      ¬ WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H.δ₀ := by
  have hno : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj 0)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map' 0 1) i).val ≠ 0 := by
    intro i hi hz
    have hmin := walkingAdjunctionFirstBottomMergeIndex_minimal H
      (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd
      (show WalkingAdjunctionBottomMergeAt H 0 from ⟨i, hi, hz⟩)
    exact hk (le_antisymm hmin (Fin.zero_le _))
  have hca : walkingAdjunctionOrdinalCard .minus Y (H.obj 0) ≤ 2 := by
    have hc := (walkingAdjunctionAtomic_endpoint_cards H ha).1
    cases Y <;> simp only [walkingAdjunctionTargetCorrection] at hc <;> omega
  have hi := ordinalInjective_of_le_two_bottom_no_one _ hca
    (walkingAdjunctionOrderHom_bottom (H.map' 0 1)) hno
  refine ⟨walkingAdjunctionOrdinalWidth_first_face_of_injective H hi, ?_⟩
  intro hface
  have hc0 := (walkingAdjunctionAtomic_endpoint_cards H ha).1
  have hc1 := (walkingAdjunctionAtomic_endpoint_cards H.δ₀ hface).1
  change walkingAdjunctionOrdinalCard .minus Y (H.obj 1) =
    walkingAdjunctionTargetCorrection .minus + walkingAdjunctionTargetCorrection Y at hc1
  have hr := (ordinalImageCard_eq_source_iff (walkingAdjunctionOrderHom (H.map' 0 1))).mpr hi
  have hv : ordinalMapVariation (walkingAdjunctionOrderHom (H.map' 0 1)) = 0 := by
    unfold ordinalMapVariation
    rw [hr]
    change walkingAdjunctionOrdinalCard .minus Y (H.obj 0) +
      walkingAdjunctionOrdinalCard .minus Y (H.obj 1) -
      2 * walkingAdjunctionOrdinalCard .minus Y (H.obj 0) = 0
    omega
  exact ((walkingAdjunctionHomShape_nondegenerate_iff_no_isIso H).mp hnd 0)
    ((walkingAdjunctionMapVariation_zero_iff_isIso _).mp hv)

end SerrePositivity.InfinityCategories.HA.Monads

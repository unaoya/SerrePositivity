module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowLastFace
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidth

/-!
概要：非退化な実原子の最後の境界面は原子的ではない。
方針：最後の面も原子的なら元の最後の実辺は一点から一点となり、実同型となる。
規約：元の四つのHomと全正の次数を扱う。
使われ方：Riehl–Verity Proposition 4.2.15の最後の実境界面、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実境界面の原子分解。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：一点から一点への元の実射は同型。
方針：実有限順序表示の全射性で像の個数を回収し、実変化量0から戻す。
規約：四つの実Hom。使われ方：Riehl–Verity §4.2の実最後の辺の退化の検出。 -/
lemma walkingAdjunctionHom_isIso_of_card_one {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f : A ⟶ B)
    (ha : walkingAdjunctionOrdinalCard X Y A = 1)
    (hb : walkingAdjunctionOrdinalCard X Y B = 1) : IsIso f := by
  have hs : Function.Surjective (walkingAdjunctionOrderHom f) := by
    intro j
    let i : Fin (walkingAdjunctionOrdinalCard X Y A) := ⟨0, by omega⟩
    refine ⟨i, Fin.ext ?_⟩
    have hj := j.isLt
    have hi := (walkingAdjunctionOrderHom f i).isLt
    omega
  have hr := (ordinalImageCard_eq_target_iff (walkingAdjunctionOrderHom f)).mpr hs
  apply (walkingAdjunctionMapVariation_zero_iff_isIso f).mp
  unfold ordinalMapVariation
  rw [hr]
  omega

/-- 概要：非退化な実原子の最後の境界面は、元の水平合成について原子的ではない。
方針：原子性から最後の二つの実対象が一点となることを回収し、実最後の辺の非同型性と比較する。
規約：最後の面の非退化性は仮定しない。使われ方：Riehl–Verity §4.2の実原子分解の必要性。 -/
lemma walkingAdjunctionLastFace_not_atomic {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) (n + 1))
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} X Y).nonDegenerate (n + 1)) :
    ¬ WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩)
      (finiteChainFace H (Fin.last (n + 1))) := by
  intro hf
  have hc := (walkingAdjunctionAtomic_endpoint_cards _ hf).2
  rw [finiteChainFace_last_obj] at hc
  have ht := (walkingAdjunctionAtomic_endpoint_cards H ha).2
  apply ((walkingAdjunctionHomShape_nondegenerate_iff_no_isIso H).mp hnd (Fin.last n))
  exact walkingAdjunctionHom_isIso_of_card_one _ hc ht

end SerrePositivity.InfinityCategories.HA.Monads

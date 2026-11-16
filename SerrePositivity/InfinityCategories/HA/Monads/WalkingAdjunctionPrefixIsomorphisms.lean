module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParent
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionIsoDegeneracy
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionHorizontalFaithful

/-!
概要：minusからplusへの固定した実対象の前置は同型と実全単体の非退化性を反映する。
方針：個数の加法則で元の対象を回収し、実水平合成の忠実性で恒等射を回収する。
規約：任意の同型の反映を新しい仮定に置かない。
使われ方：Riehl–Verity Lemma 4.1.4の始点plusの親、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実非退化性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：固定したminusからplusへの実対象の前置は実射の同型性を反映する。
方針：個数から元の両対象を同一視し、剛性と水平合成の忠実性で元の射を恒等射へ戻す。
規約：元の四Homの同型性。使われ方：Riehl–Verity Lemma 4.1.4の前置。 -/
lemma walkingAdjunctionPrefix_reflectsIsIso {Y : WalkingAdjunctionPoint}
    (U : walkingAdjunctionHom .minus .plus) {A B : walkingAdjunctionHom .plus Y} (f : A ⟶ B)
    [IsIso ((walkingAdjunctionHorizontal .minus .plus Y).map
      (X := (U, A)) (Y := (U, B)) (𝟙 U, f))] : IsIso f := by
  have hc := walkingAdjunctionCard_eq_of_isIso
    ((walkingAdjunctionHorizontal .minus .plus Y).map (X := (U, A)) (Y := (U, B)) (𝟙 U, f))
  rw [walkingAdjunctionOrdinalCard_comp_plus, walkingAdjunctionOrdinalCard_comp_plus] at hc
  have hAB : A = B := by
    apply walkingAdjunctionWeight_injective .plus Y
    have ha := walkingAdjunctionOrdinalCard_weight .plus Y A
    have hb := walkingAdjunctionOrdinalCard_weight .plus Y B
    omega
  subst B
  obtain ⟨ho, hm⟩ := walkingAdjunctionIsIso_eqToHom
    ((walkingAdjunctionHorizontal .minus .plus Y).map (X := (U, A)) (Y := (U, A)) (𝟙 U, f))
  have he : (walkingAdjunctionHorizontal .minus .plus Y).map
      (X := (U, A)) (Y := (U, A)) (𝟙 U, f) =
      (walkingAdjunctionHorizontal .minus .plus Y).map (𝟙 U, 𝟙 A) := by
    calc
      _ = 𝟙 ((walkingAdjunctionHorizontal .minus .plus Y).obj (U, A)) := by
        simpa only [eqToHom_refl] using hm
      _ = _ := ((walkingAdjunctionHorizontal .minus .plus Y).map_id (U, A)).symm
  have hf : f = 𝟙 A := (walkingAdjunctionHorizontal_plus_map_inj .minus Y
    (𝟙 U) (𝟙 U) f (𝟙 A) he).2
  rw [hf]
  infer_instance

/-- 概要：実生成射を前置した全実単体は、元が非退化なら非退化。
方針：同型な隣接実辺を反映し、元のnerveの非退化性の判定を適用する。
規約：正の全次数。使われ方：Riehl–Verity Lemma 4.1.4の指定面。 -/
lemma walkingAdjunctionPlusParentPrefix_nondegenerate {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) (n + 1))
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .plus Y).nonDegenerate (n + 1)) :
    ULift.up (walkingAdjunctionPlusParentPrefix H) ∈
      (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1) := by
  apply (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso _).mpr
  intro j hj
  change IsIso ((walkingAdjunctionHorizontal .minus .plus Y).map
    (X := (walkingAdjunctionGeneratorVertex .minus, H.obj j.castSucc))
    (Y := (walkingAdjunctionGeneratorVertex .minus, H.obj j.succ))
    (𝟙 (walkingAdjunctionGeneratorVertex .minus),
      H.map (homOfLE (Fin.castSucc_le_succ j)))) at hj
  have := hj
  apply (walkingAdjunctionHomShape_nondegenerate_iff_no_isIso H).mp hnd j
  exact walkingAdjunctionPrefix_reflectsIsIso (walkingAdjunctionGeneratorVertex .minus)
    (H.map (homOfLE (Fin.castSucc_le_succ j)))

end SerrePositivity.InfinityCategories.HA.Monads

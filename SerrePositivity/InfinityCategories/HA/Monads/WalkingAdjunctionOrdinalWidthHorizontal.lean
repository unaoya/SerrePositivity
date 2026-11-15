module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalGlueVariation
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthPrecomp
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFactorCuts

/-!
概要：実水平合成は全実辺の変化量と有限順序の幅について加法的である。
方針：中点plusでは順序和、中点minusでは端点共有の実像の法則へ移して計算する。
規約：八つの元の実双関手と全次数の全実関手を保持する。
使われ方：Riehl–Verity Proposition 4.2.15の実原子分解の幅、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの幅の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実水平合成の個数と中点の補正の和は、左右の実個数の和。
方針：元の実水平合成の重みと個数の法則を合わせる。
規約：八つの実水平合成。使われ方：Riehl–Verity §4.2の幅の補正の計算。 -/
lemma walkingAdjunctionOrdinalCard_comp_correction (X M Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X M) (B : walkingAdjunctionHom M Y) :
    walkingAdjunctionOrdinalCard X Y ((walkingAdjunctionHorizontal X M Y).obj (A, B)) +
      walkingAdjunctionTargetCorrection M =
    walkingAdjunctionOrdinalCard X M A + walkingAdjunctionOrdinalCard M Y B := by
  have hw := walkingAdjunctionHorizontal_weight X M Y A B
  have hc := walkingAdjunctionOrdinalCard_weight X Y
    ((walkingAdjunctionHorizontal X M Y).obj (A, B))
  have ha := walkingAdjunctionOrdinalCard_weight X M A
  have hb := walkingAdjunctionOrdinalCard_weight M Y B
  omega

/-- 概要：実水平合成の実辺の変化量は左右の実辺の変化量の和。
方針：実順序和または端点共有の射の表示を移し、それぞれの加法性を使う。
規約：元の八つの実双関手の全射。使われ方：Riehl–Verity §4.2の実分解の幅。 -/
lemma walkingAdjunctionHorizontal_variation (X M Y : WalkingAdjunctionPoint)
    {A A' : walkingAdjunctionHom X M} {B B' : walkingAdjunctionHom M Y}
    (f : A ⟶ A') (g : B ⟶ B') :
    ordinalMapVariation (walkingAdjunctionOrderHom ((walkingAdjunctionHorizontal X M Y).map
      (X := (A, B)) (Y := (A', B')) (f, g))) =
    ordinalMapVariation (walkingAdjunctionOrderHom f) +
      ordinalMapVariation (walkingAdjunctionOrderHom g) := by
  cases M with
  | plus =>
    exact (ordinalMapVariation_heq (walkingAdjunctionOrdinalCard_comp_plus X Y A B)
      (walkingAdjunctionOrdinalCard_comp_plus X Y A' B') _ _
      (walkingAdjunctionOrderHom_comp_plus X Y f g)).trans
        (ordinalMapVariation_append (walkingAdjunctionOrderHom f) (walkingAdjunctionOrderHom g))
  | minus =>
    have hv := ordinalMapVariation_heq (walkingAdjunctionOrdinalCard_comp_minus X Y A B)
      (walkingAdjunctionOrdinalCard_comp_minus X Y A' B') _ _
      (walkingAdjunctionOrderHom_comp_minus X Y f g)
    rw [ordinalMapVariation_glue _ _ (walkingAdjunctionIncomingMap_last f)
      (walkingAdjunctionOutgoingMap_zero g)] at hv
    have hf := ordinalMapVariation_heq (walkingAdjunctionIncoming_card X A).symm
      (walkingAdjunctionIncoming_card X A').symm _ _ (walkingAdjunctionIncomingMap_heq f)
    have hg := ordinalMapVariation_heq (walkingAdjunctionOutgoing_card Y B).symm
      (walkingAdjunctionOutgoing_card Y B').symm _ _ (walkingAdjunctionOutgoingMap_heq g)
    exact hv.trans (congrArg₂ (fun a b : ℕ => a + b) hf hg)

/-- 概要：実水平合成の全実辺の変化量の和は左右の全実辺の和に等しい。
方針：各実辺の加法性を全有限添字で足す。
規約：全次数の全実関手。使われ方：Riehl–Verity §4.2の実原子の合成の幅。 -/
lemma walkingAdjunctionHorizontal_variation_sum {n : ℕ} (X M Y : WalkingAdjunctionPoint)
    (F : ComposableArrows (walkingAdjunctionHom X M) n)
    (G : ComposableArrows (walkingAdjunctionHom M Y) n) :
    (∑ j : Fin n, ordinalMapVariation (walkingAdjunctionOrderHom
      ((F.prod' G ⋙ walkingAdjunctionHorizontal X M Y).map
        (homOfLE (Fin.castSucc_le_succ j))))) =
      (∑ j : Fin n, ordinalMapVariation
        (walkingAdjunctionOrderHom (F.map (homOfLE (Fin.castSucc_le_succ j))))) +
      ∑ j : Fin n, ordinalMapVariation
        (walkingAdjunctionOrderHom (G.map (homOfLE (Fin.castSucc_le_succ j)))) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact walkingAdjunctionHorizontal_variation X M Y _ _

/-- 概要：実水平合成の有限順序の幅は左右の幅の和。
方針：全実辺の変化量と両端の個数の補正の加法性を合わせる。
規約：八つの実合成・全次数。使われ方：Riehl–Verity Proposition 4.2.15の実分解の幅。 -/
lemma walkingAdjunctionOrdinalWidth_horizontal {n : ℕ} (X M Y : WalkingAdjunctionPoint)
    (F : ComposableArrows (walkingAdjunctionHom X M) n)
    (G : ComposableArrows (walkingAdjunctionHom M Y) n) :
    walkingAdjunctionOrdinalWidth (F.prod' G ⋙ walkingAdjunctionHorizontal X M Y) =
      walkingAdjunctionOrdinalWidth F + walkingAdjunctionOrdinalWidth G := by
  have h0 := walkingAdjunctionOrdinalCard_comp_correction X M Y (F.obj 0) (G.obj 0)
  have hn := walkingAdjunctionOrdinalCard_comp_correction X M Y
    (F.obj (Fin.last n)) (G.obj (Fin.last n))
  have hf := walkingAdjunctionCard_pair_corrections_le X M (F.obj 0) (F.obj (Fin.last n))
  have hg := walkingAdjunctionCard_pair_corrections_le M Y (G.obj 0) (G.obj (Fin.last n))
  have hc := walkingAdjunctionCard_pair_corrections_le X Y
    ((walkingAdjunctionHorizontal X M Y).obj (F.obj 0, G.obj 0))
    ((walkingAdjunctionHorizontal X M Y).obj (F.obj (Fin.last n), G.obj (Fin.last n)))
  let sf := ∑ j : Fin n, ordinalMapVariation
    (walkingAdjunctionOrderHom (F.map (homOfLE (Fin.castSucc_le_succ j))))
  let sg := ∑ j : Fin n, ordinalMapVariation
    (walkingAdjunctionOrderHom (G.map (homOfLE (Fin.castSucc_le_succ j))))
  unfold walkingAdjunctionOrdinalWidth
  rw [walkingAdjunctionHorizontal_variation_sum]
  change (walkingAdjunctionOrdinalCard X Y
        ((walkingAdjunctionHorizontal X M Y).obj (F.obj 0, G.obj 0)) +
      walkingAdjunctionOrdinalCard X Y ((walkingAdjunctionHorizontal X M Y).obj
        (F.obj (Fin.last n), G.obj (Fin.last n))) -
      (walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y) + (sf + sg)) =
    (walkingAdjunctionOrdinalCard X M (F.obj 0) +
      walkingAdjunctionOrdinalCard X M (F.obj (Fin.last n)) -
        (walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection M) + sf) +
    (walkingAdjunctionOrdinalCard M Y (G.obj 0) +
      walkingAdjunctionOrdinalCard M Y (G.obj (Fin.last n)) -
        (walkingAdjunctionTargetCorrection M + walkingAdjunctionTargetCorrection Y) + sg)
  omega

/-- 概要：実水平分解の有限順序の幅は左右の実因子の幅の和。
方針：実分解の全合成の等式を元の実水平合成の幅の式へ移す。
規約：全実関手の分解。使われ方：Riehl–Verity §4.2の実原子分解の幅の境界。 -/
lemma WalkingAdjunctionFactorization.ordinalWidth {n : ℕ} {X Y : WalkingAdjunctionPoint}
    {H : ComposableArrows (walkingAdjunctionHom X Y) n} (a : WalkingAdjunctionFactorization H) :
    walkingAdjunctionOrdinalWidth H =
      walkingAdjunctionOrdinalWidth a.left + walkingAdjunctionOrdinalWidth a.right :=
  (congrArg walkingAdjunctionOrdinalWidth a.fac).symm.trans
    (walkingAdjunctionOrdinalWidth_horizontal X a.middle Y a.left a.right)

end SerrePositivity.InfinityCategories.HA.Monads

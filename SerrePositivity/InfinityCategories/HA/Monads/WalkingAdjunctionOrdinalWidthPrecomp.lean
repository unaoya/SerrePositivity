module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidth
public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinementFaces
public import Mathlib.Algebra.BigOperators.Fin

/-!
概要：実全鎖の先頭へ実射を挿入したときの、有限順序の幅の変化を計算する。
方針：全実辺の変化量の有限和を先頭と尾部へ分け、両端の個数の式を比較する。
規約：実対象の等式による係数移送も保持する。
使われ方：Riehl–Verity Proposition 4.2.15の実親の幅の法則、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの計算。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：両端と実射の異種等式に沿う係数移送は実辺の変化量を保つ。
方針：両端の実対象と実射を同一視する。
規約：同じ二対象のHomで比較する。使われ方：Riehl–Verity §4.2の実幅の移送。 -/
lemma walkingAdjunctionMapVariation_heq {X Y : WalkingAdjunctionPoint}
    {A B A' B' : walkingAdjunctionHom X Y} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : HEq f g) :
    ordinalMapVariation (walkingAdjunctionOrderHom f) =
      ordinalMapVariation (walkingAdjunctionOrderHom g) := by
  subst A'
  subst B'
  have he : f = g := eq_of_heq h
  subst g
  rfl

/-- 概要：二つの実対象の個数の和は、始点と終点の補正の和以上。
方針：minusに接する実Homの非空性を使う。
規約：plus自己Homの空の対象も含む。使われ方：Riehl–Verity §4.2の幅の減算の検収。 -/
lemma walkingAdjunctionCard_pair_corrections_le (X Y : WalkingAdjunctionPoint)
    (A B : walkingAdjunctionHom X Y) :
    walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y ≤
      walkingAdjunctionOrdinalCard X Y A + walkingAdjunctionOrdinalCard X Y B := by
  cases X <;> cases Y
  · change 0 + 0 ≤ _
    omega
  · have ha := NeZero.pos (walkingAdjunctionOrdinalCard .plus .minus A)
    change 0 + 1 ≤ _
    omega
  · have ha := NeZero.pos (walkingAdjunctionOrdinalCard .minus .plus A)
    change 1 + 0 ≤ _
    omega
  · have ha := NeZero.pos (walkingAdjunctionOrdinalCard .minus .minus A)
    have hb := NeZero.pos (walkingAdjunctionOrdinalCard .minus .minus B)
    change 1 + 1 ≤ _
    omega

/-- 概要：先頭へ実射を挿入すると全実辺の変化量の和はその変化量だけ増える。
方針：有限和を先頭と尾部へ分け、実precompの射を評価する。
規約：全実辺を含む。使われ方：Riehl–Verity §4.2の実細分の幅の照合。 -/
lemma walkingAdjunctionPrecomp_variation_sum {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) {A : walkingAdjunctionHom X Y}
    (f : A ⟶ H.left) :
    (∑ j : Fin (n + 1), ordinalMapVariation
      (walkingAdjunctionOrderHom ((H.precomp f).map (homOfLE (Fin.castSucc_le_succ j))))) =
    ordinalMapVariation (walkingAdjunctionOrderHom f) +
      ∑ j : Fin n, ordinalMapVariation
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j)))) := by
  rw [Fin.sum_univ_succ]
  rfl

/-- 概要：先頭への実射の挿入による有限順序の幅の変化は実両端と実射の変化量で決まる。
方針：変化量の有限和の分割と、両端の個数からの補正の減算を計算する。
規約：全次数・空の対象も含む。使われ方：Riehl–Verity §4.2の実親の幅の保存。 -/
lemma walkingAdjunctionOrdinalWidth_precomp {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n) {A : walkingAdjunctionHom X Y}
    (f : A ⟶ H.left) :
    walkingAdjunctionOrdinalWidth (H.precomp f) + walkingAdjunctionOrdinalCard X Y H.left =
      walkingAdjunctionOrdinalWidth H + walkingAdjunctionOrdinalCard X Y A +
        ordinalMapVariation (walkingAdjunctionOrderHom f) := by
  have hh := walkingAdjunctionCard_pair_corrections_le X Y H.left (H.obj (Fin.last n))
  have hp := walkingAdjunctionCard_pair_corrections_le X Y A (H.obj (Fin.last n))
  change walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y ≤
    walkingAdjunctionOrdinalCard X Y (H.obj 0) +
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) at hh
  unfold walkingAdjunctionOrdinalWidth
  rw [walkingAdjunctionPrecomp_variation_sum]
  change (walkingAdjunctionOrdinalCard X Y A +
      walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) -
        (walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y) +
      (ordinalMapVariation (walkingAdjunctionOrderHom f) + _)) +
      walkingAdjunctionOrdinalCard X Y (H.obj 0) = _
  omega

end SerrePositivity.InfinityCategories.HA.Monads

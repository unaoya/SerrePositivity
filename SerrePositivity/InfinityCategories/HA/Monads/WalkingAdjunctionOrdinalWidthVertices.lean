module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthPrecomp

/-!
概要：実全鎖の各頂点の個数と重みを、有限順序の幅で押さえる。
方針：一辺の個数の差の上限を尾部の帰納で足し、原子の両端の式を使う。
規約：原典の文字列との全比較は別に行い、元の実関手の全頂点を扱う。
使われ方：Riehl–Verity Proposition 4.2.15の各幅での有限性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの有限の境界。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：全実頂点の個数は始点の個数と全実辺の変化量の和以下。
方針：先頭の辺の個数の差を、尾部の全頂点の境界に足す。
規約：全次数・全実頂点。使われ方：Riehl–Verity §4.2の実幅での個数の境界。 -/
lemma walkingAdjunctionVertexCard_le_first_add_variation {X Y : WalkingAdjunctionPoint} :
    ∀ (n : ℕ) (H : ComposableArrows (walkingAdjunctionHom X Y) n) (i : Fin (n + 1)),
      walkingAdjunctionOrdinalCard X Y (H.obj i) ≤
        walkingAdjunctionOrdinalCard X Y (H.obj 0) +
          ∑ j : Fin n, ordinalMapVariation
            (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j)))) := by
  intro n
  induction n with
  | zero =>
    intro H i
    have hi : i = 0 := by apply Fin.ext; have hlt := i.isLt; change i.val = 0; omega
    subst i
    simp
  | succ n ih =>
    intro H i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.le_add_right _ _
    · have hi := ih H.δ₀ j
      have he := ordinalMapVariation_target_le (walkingAdjunctionOrderHom (H.map' 0 1))
      have hs := walkingAdjunctionPrecomp_variation_sum H.δ₀ (H.map' 0 1)
      rw [composableArrowPrecomp_decompose] at hs
      change walkingAdjunctionOrdinalCard X Y (H.obj j.succ) ≤
        walkingAdjunctionOrdinalCard X Y (H.obj 1) + _ at hi
      change walkingAdjunctionOrdinalCard X Y (H.obj 1) ≤
        walkingAdjunctionOrdinalCard X Y (H.obj 0) + _ at he
      omega

/-- 概要：実原子の全頂点の個数は有限順序の幅と両端の補正の和より小さい。
方針：実始点の個数と実原子の幅の式を全辺の境界へ適用する。
規約：全実頂点の厳密な上限。使われ方：Riehl–Verity §4.2の各幅での有限性。 -/
lemma walkingAdjunctionOrdinalWidth_vertex_card_lt {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) (i : Fin (n + 1)) :
    walkingAdjunctionOrdinalCard X Y (H.obj i) < walkingAdjunctionOrdinalWidth H +
      walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y := by
  have hb := walkingAdjunctionVertexCard_le_first_add_variation n H i
  have hf := (walkingAdjunctionAtomic_endpoint_cards H ha).1
  have hw := walkingAdjunctionOrdinalWidth_atomic H ha
  omega

/-- 概要：実原子の全頂点の重みは有限順序の幅以下。
方針：実個数と重みの補正の式を、全頂点の個数の上限へ戻す。
規約：四Homの全実頂点。使われ方：Riehl–Verity §4.2の実対象の有限の範囲。 -/
lemma walkingAdjunctionOrdinalWidth_vertex_weight_le {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom X Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨X⟩) (Y := ⟨Y⟩) H) (i : Fin (n + 1)) :
    walkingAdjunctionWeight X Y (H.obj i) ≤ walkingAdjunctionOrdinalWidth H := by
  have hb := walkingAdjunctionOrdinalWidth_vertex_card_lt H ha i
  have hc := walkingAdjunctionOrdinalCard_weight X Y (H.obj i)
  have hx : walkingAdjunctionTargetCorrection X ≤ 1 := by cases X <;> decide
  omega

end SerrePositivity.InfinityCategories.HA.Monads

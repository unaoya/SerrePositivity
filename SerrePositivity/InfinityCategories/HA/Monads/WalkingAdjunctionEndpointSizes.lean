module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicCuts
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionCutBounds

/-!
概要：実全単体の正の長さと、始頂点・終頂点の有限点の個数の境界を照合する。
方針：長さと個数の補正の関係、元の全射と端点保存を使う。
規約：原子性に使う正の長さを別の存在の仮定へ置き換えない。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の構成、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の原子の有限端点による表示。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実対象の長さは点の個数の二倍から両端の補正を除いたもの。
方針：重みを介する既存の二つの法則を合わせる。規約：四Hom全て。
使われ方：Riehl–Verity §4.1の端点の個数の算術。 -/
lemma walkingAdjunctionVertexLength_card (X Y : WalkingAdjunctionPoint)
    (A : walkingAdjunctionHom X Y) :
    walkingAdjunctionVertexLength X Y A + walkingAdjunctionTargetCorrection X +
      walkingAdjunctionTargetCorrection Y = 2 * walkingAdjunctionOrdinalCard X Y A := by
  have hl := walkingAdjunctionVertexLength_weight X Y A
  have hc := walkingAdjunctionOrdinalCard_weight X Y A
  omega

/-- 概要：長さが正の実全単体の終頂点には実点がある。
方針：終頂点が空なら各頂点からの実射の表示で全頂点が空となる。
規約：全射の存在は元の実関手から取る。使われ方：Riehl–Verity §4.1の原子の端点。 -/
lemma walkingAdjunctionLastCard_pos_of_size_pos {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y) (hp : 0 < walkingAdjunctionLevelSize H) :
    0 < walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) := by
  by_contra hn
  have hz : walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 0 := by omega
  have hc (i : Fin (n + 1)) : walkingAdjunctionOrdinalCard X Y (H.obj i) = 0 := by
    by_contra hi
    have hi' : 0 < walkingAdjunctionOrdinalCard X Y (H.obj i) := by omega
    have he := (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.le_last i))) ⟨0, hi'⟩).isLt
    omega
  have hs : walkingAdjunctionLevelSize H = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hl := walkingAdjunctionVertexLength_card X Y (H.obj i)
    rw [hc i] at hl
    omega
  omega

/-- 概要：minus自己Homの正の長さの全単体の始頂点には二つ以上の実点がある。
方針：始頂点の点が一つなら最小・最大元の保存が全頂点の個数を1にする。
規約：両端の保存は元の全射から取る。使われ方：Riehl–Verity §4.1の原子の始端。 -/
lemma walkingAdjunctionMinusFirstCard_two_le_of_size_pos {n : ℕ}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom .minus .minus)
    (hp : 0 < walkingAdjunctionLevelSize H) :
    2 ≤ walkingAdjunctionOrdinalCard .minus .minus (H.obj 0) := by
  by_contra hn
  have hpos := NeZero.pos (walkingAdjunctionOrdinalCard .minus .minus (H.obj 0))
  have hone : walkingAdjunctionOrdinalCard .minus .minus (H.obj 0) = 1 := by omega
  let z : Fin (walkingAdjunctionOrdinalCard .minus .minus (H.obj 0)) := ⟨0, hpos⟩
  have hc (i : Fin (n + 1)) : walkingAdjunctionOrdinalCard .minus .minus (H.obj i) = 1 := by
    have hb := walkingAdjunctionOrderHom_bottom (H.map (homOfLE (Fin.zero_le i))) z rfl
    have ht := walkingAdjunctionOrderHom_top (H.map (homOfLE (Fin.zero_le i))) z
      (by change 0 + 1 = _; omega)
    omega
  have hs : walkingAdjunctionLevelSize H = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hl := walkingAdjunctionVertexLength_card .minus .minus (H.obj i)
    rw [hc i] at hl
    change walkingAdjunctionVertexLength .minus .minus (H.obj i) + 1 + 1 = 2 * 1 at hl
    omega
  omega

/-- 概要：正の長さの全単体の始頂点の個数は両端の補正の和以上。
方針：混合Homの非空性とminus自己Homの二点の境界を合わせる。
規約：plus自己Homは空を許す。使われ方：Riehl–Verity §4.1の原子の始端の下限。 -/
lemma walkingAdjunctionFirstCard_corrections_le_of_size_pos {n : ℕ}
    {X Y : WalkingAdjunctionPoint} (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hp : 0 < walkingAdjunctionLevelSize H) :
    walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y ≤
      walkingAdjunctionOrdinalCard X Y (H.obj 0) := by
  cases X <;> cases Y
  · change 0 + 0 ≤ _
    omega
  · exact NeZero.pos (walkingAdjunctionOrdinalCard .plus .minus (H.obj 0))
  · exact NeZero.pos (walkingAdjunctionOrdinalCard .minus .plus (H.obj 0))
  · exact walkingAdjunctionMinusFirstCard_two_le_of_size_pos H hp

/-- 概要：指定の二つの端点の個数は全単体の正の長さを保証する。
方針：長さ0なら両端の長さ0を代入して矛盾する。規約：全頂点を捨てていない。
使われ方：Riehl–Verity §4.1の原子の端点による判定の正の長さ。 -/
lemma walkingAdjunctionSize_pos_of_endpoint_cards {n : ℕ} {X Y : WalkingAdjunctionPoint}
    (H : Fin (n + 1) ⥤ walkingAdjunctionHom X Y)
    (hfirst : walkingAdjunctionOrdinalCard X Y (H.obj 0) =
      walkingAdjunctionTargetCorrection X + walkingAdjunctionTargetCorrection Y)
    (hlast : walkingAdjunctionOrdinalCard X Y (H.obj (Fin.last n)) = 1) :
    0 < walkingAdjunctionLevelSize H := by
  by_contra hn
  have hz : walkingAdjunctionLevelSize H = 0 := by omega
  have h0 := walkingAdjunctionLevelSize_vertex_zero H hz 0
  have hn := walkingAdjunctionLevelSize_vertex_zero H hz (Fin.last n)
  have hc0 := walkingAdjunctionVertexLength_card X Y (H.obj 0)
  have hcn := walkingAdjunctionVertexLength_card X Y (H.obj (Fin.last n))
  omega

end SerrePositivity.InfinityCategories.HA.Monads

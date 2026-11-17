module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthVertices
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOnePointDegeneracy

/-!
概要：minusからplusへの幅1の実全鎖は実生成射の定値関手そのものである。
方針：両端の非空性で全辺の変化量を0にし、全頂点の実個数を1へ押さえる。
規約：原子性・非退化性を入力にしない。
使われ方：Riehl–Verity Proposition 4.2.15の親の幅が一致する境界の場合、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実生成射の回収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：minusからplusへの幅1の全実関手は、同じ実生成射の定値関手と等しい。
方針：非空の両端と幅の式から全変化量を0、全頂点の境界から各実個数を1にする。
規約：同型類ではなく全関手の等式。使われ方：Riehl–Verity §4.2の境界での幅1の因子。 -/
lemma walkingAdjunctionWidthOne_minus_plus_generator {n : ℕ}
    (H : ComposableArrows (walkingAdjunctionHom .minus .plus) n)
    (hw : walkingAdjunctionOrdinalWidth H = 1) :
    H = (Functor.const (Fin (n + 1))).obj (walkingAdjunctionGeneratorVertex .minus) := by
  let s := ∑ j : Fin n, ordinalMapVariation
    (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ j))))
  have h0 := NeZero.pos (walkingAdjunctionOrdinalCard .minus .plus (H.obj 0))
  have hn := NeZero.pos (walkingAdjunctionOrdinalCard .minus .plus (H.obj (Fin.last n)))
  have hw' : walkingAdjunctionOrdinalCard .minus .plus (H.obj 0) +
      walkingAdjunctionOrdinalCard .minus .plus (H.obj (Fin.last n)) - 1 + s = 1 := hw
  have hc0 : walkingAdjunctionOrdinalCard .minus .plus (H.obj 0) = 1 := by omega
  have hs : s = 0 := by omega
  have hc (i : Fin (n + 1)) : walkingAdjunctionOrdinalCard .minus .plus (H.obj i) = 1 := by
    have hi := walkingAdjunctionVertexCard_le_first_add_variation n H i
    change walkingAdjunctionOrdinalCard .minus .plus (H.obj i) ≤
      walkingAdjunctionOrdinalCard .minus .plus (H.obj 0) + s at hi
    have hp := NeZero.pos (walkingAdjunctionOrdinalCard .minus .plus (H.obj i))
    omega
  have hobj : H.obj 0 = walkingAdjunctionGeneratorVertex .minus := by
    apply walkingAdjunctionOrdinalCard_injective .minus .plus
    exact (hc 0).trans rfl
  exact (walkingAdjunctionConst_of_card_one H hc).trans
    (congrArg (fun A => (Functor.const (Fin (n + 1))).obj A) hobj)

end SerrePositivity.InfinityCategories.HA.Monads

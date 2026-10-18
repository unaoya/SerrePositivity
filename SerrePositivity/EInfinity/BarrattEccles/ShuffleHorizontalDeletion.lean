module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleDeletePosition

/-!
# 水平辺の削除による shuffle の対応

概要：Berger–Fresse §1.1.3 の水平辺の削除を、shuffle 経路の間の同値として構成する。
方針：指定位置へ水平辺を挿入する操作と、その辺を削除して位置番号を詰める操作を使う。
規約：水平辺数 p+1 の経路から一辺を削除すると水平辺数 p の経路となる。
使われ方：水平な同方向の境界面を小さい shuffle の有限和へ添字替えする。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：指定位置に水平辺を持つ大きい経路と小さい経路の同値（Berger–Fresse §1.1.3）。
方針：有限辺集合の挿入・削除の逆性を、辺数の次数同定を介して用いる。
規約：辺位置 a は大きい経路の番号で固定する。
使われ方：水平辺を削除する境界項の添字替えの基礎となる。 -/
def horizontalInsertionEquiv (p q : ℕ) (a : Fin (p + 1 + q)) :
    ShufflePath p q ≃ {s : ShufflePath (p + 1) q // a ∈ s.val} := by
  let e : Fin (p + 1 + q) ≃ Fin (p + q + 1) := finCongr (by omega)
  let F := e.finsetCongr
  refine {
    toFun := fun s => ?_
    invFun := fun s => ?_
    left_inv := fun s => ?_
    right_inv := fun s => ?_ }
  · refine ⟨⟨F.symm (insertPosition s.val (e a)), ?_⟩, ?_⟩
    · change ((insertPosition s.val (e a)).map e.symm.toEmbedding).card = p + 1
      rw [Finset.card_map, insertPosition_card, s.property]
    · change a ∈ (insertPosition s.val (e a)).map e.symm.toEmbedding
      rw [Finset.mem_map_equiv]
      exact mem_insertPosition s.val (e a)
  · have ha : e a ∈ F s.val.val := (Finset.mem_map' e.toEmbedding).2 s.property
    refine ⟨erasePosition (F s.val.val) (e a), ?_⟩
    rw [erasePosition_card, Finset.card_erase_of_mem ha]
    change (s.val.val.map e.toEmbedding).card - 1 = p
    rw [Finset.card_map, s.val.property]
    omega
  · apply Subtype.ext
    change erasePosition (F (F.symm (insertPosition s.val (e a)))) (e a) = s.val
    rw [F.apply_symm_apply, erasePosition_insertPosition]
  · apply Subtype.ext
    apply Subtype.ext
    change F.symm (insertPosition (erasePosition (F s.val.val) (e a)) (e a)) = s.val.val
    have ha : e a ∈ F s.val.val := (Finset.mem_map' e.toEmbedding).2 s.property
    rw [insertPosition_erasePosition _ _ ha, F.symm_apply_apply]

end SerrePositivity.EInfinity.BarrattEccles

module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCastCoordinates

/-!
# shuffle の二つの方向の交換

概要：Berger–Fresse §1.1.3 の二入力の交換を格子経路の水平・垂直の交換で表す。
方針：水平辺集合の補集合を取り、全辺数の加法の交換則で移送する。
規約：辺の位置を変えず、水平・垂直の色だけを交換する。
使われ方：異なる入力への二つの代入の並列結合則の添字替えを構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：shuffle の水平・垂直の方向を交換する（Berger–Fresse §1.1.3）。
方針：水平辺の補集合を新しい水平辺とする。
規約：経路の長さ p+q は q+p へ移送する。
使われ方：三入力の最後の二入力の交換の添字となる。 -/
def ShufflePath.exchange {p q : ℕ} (s : ShufflePath p q) : ShufflePath q p :=
  ⟨s.valᶜ.map (finCongr (Nat.add_comm p q)).toEmbedding, by
    rw [Finset.card_map, s.compl_card]⟩

/-- 概要：経路の方向を二回交換すると元へ戻る（Berger–Fresse §1.1.3）。
方針：移送と補集合の交換および二回の補集合を相殺する。
規約：辺の位置の二回の次数移送も恒等となる。
使われ方：方向の交換を全単射にする。 -/
@[simp] lemma ShufflePath.exchange_exchange {p q : ℕ} (s : ShufflePath p q) :
    s.exchange.exchange = s := by
  apply Subtype.ext
  change (s.valᶜ.map (finCongr (Nat.add_comm p q)).toEmbedding)ᶜ.map
    (finCongr (Nat.add_comm q p)).toEmbedding = s.val
  rw [map_finCongr_compl, compl_compl, Finset.map_map]
  have he : (finCongr (Nat.add_comm p q)).toEmbedding.trans
      (finCongr (Nat.add_comm q p)).toEmbedding = Function.Embedding.refl _ := by
    ext x
    simp
  rw [he, Finset.map_refl]

/-- 概要：方向の交換は shuffle 経路の全単射である（Berger–Fresse §1.1.3）。
方針：逆写像にも同じ方向の交換を使う。
規約：始域は (p,q)、終域は (q,p) の経路である。
使われ方：交換した二入力の shuffle 和の添字替えを行う。 -/
def shuffleExchangeEquiv (p q : ℕ) : ShufflePath p q ≃ ShufflePath q p where
  toFun := ShufflePath.exchange
  invFun := ShufflePath.exchange
  left_inv := ShufflePath.exchange_exchange
  right_inv := ShufflePath.exchange_exchange

/-- 概要：方向の交換は水平座標を元の垂直座標にする（Berger–Fresse §1.1.3）。
方針：補集合を移送した辺集合の接頭濃度を計算する。
規約：頂点番号の値は移送で変わらない。
使われ方：交換後の三入力の各頂点の座標を同定する。 -/
lemma ShufflePath.exchange_horizontal {p q : ℕ} (s : ShufflePath p q)
    (a : Fin (p + q + 1)) :
    s.exchange.horizontal (Fin.cast (by omega : p + q + 1 = q + p + 1) a) = s.vertical a := by
  apply Fin.ext
  change ((s.valᶜ.map (finCongr (Nat.add_comm p q)).toEmbedding).filter
    (fun x => x.val < a.val)).card = (s.valᶜ.filter (fun x => x.val < a.val)).card
  exact card_filter_finCongr _ _ _

/-- 概要：方向の交換は垂直座標を元の水平座標にする（Berger–Fresse §1.1.3）。
方針：水平座標の交換と二座標の和の公式を比較する。
規約：頂点の移送には加法の交換則を使う。
使われ方：交換した入力を使う shuffle 単体を比較する。 -/
lemma ShufflePath.exchange_vertical {p q : ℕ} (s : ShufflePath p q)
    (a : Fin (p + q + 1)) :
    s.exchange.vertical (Fin.cast (by omega : p + q + 1 = q + p + 1) a) = s.horizontal a := by
  apply Fin.ext
  have hh := congrArg Fin.val (s.exchange_horizontal a)
  have h₁ := s.coordinate_sum a
  have h₂ := s.exchange.coordinate_sum (Fin.cast (by omega : p + q + 1 = q + p + 1) a)
  simp only [Fin.val_cast] at h₂
  omega

end SerrePositivity.EInfinity.BarrattEccles

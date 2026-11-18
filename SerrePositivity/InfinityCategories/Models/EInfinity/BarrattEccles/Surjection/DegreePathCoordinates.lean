module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePaths

/-!
模型。文献の定義との比較は後で
# 実際の成分経路の連結と頂点座標

概要：Berger–Fresse §1.5.4 の経路連結で、前半・後半の水平・垂直座標を計算する。
方針：既存の連結辺集合の接頭濃度公式を実際の経路座標へ移す。
規約：共有切断頂点は両側の式で同じ座標を持つ。
使われ方：融合行列の成分連結と compositionPath の全頂点を照合する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.SimplicialChains.Shuffle

/-- 概要：連結経路の前半の水平座標は元の前半の水平座標（BF §1.5.4）。
方針：前半の接頭水平辺数を使う。
規約：前半の最後の頂点も含む。
使われ方：最初の水平・垂直成分の元の置換添字。 -/
lemma append_horizontal_front {p q r s : ℕ} (a : ShufflePath p q) (b : ShufflePath r s)
    (k : Fin (p + q + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append a b).horizontal ⟨k.val, by have := k.isLt; omega⟩).val =
      (a.horizontal k).val := by
  change ((_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin a.val b.val (by omega)).filter (fun i => i.val < k.val)).card =
    (a.val.filter (fun i => i.val < k.val)).card
  exact _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin_prefix_card_front _ _ _ k.val (by have := k.isLt; omega)

/-- 概要：連結経路の前半の垂直座標は元の前半の垂直座標（BF §1.5.4）。
方針：補集合の連結と前半の接頭辺数を使う。
規約：前半の最後の頂点も含む。
使われ方：前半成分で固定する内側の置換添字。 -/
lemma append_vertical_front {p q r s : ℕ} (a : ShufflePath p q) (b : ShufflePath r s)
    (k : Fin (p + q + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append a b).vertical ⟨k.val, by have := k.isLt; omega⟩).val =
      (a.vertical k).val := by
  change ((_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin a.val b.val (by omega))ᶜ.filter (fun i => i.val < k.val)).card =
    (a.valᶜ.filter (fun i => i.val < k.val)).card
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin_compl]
  exact _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin_prefix_card_front _ _ _ k.val (by have := k.isLt; omega)

/-- 概要：連結経路の後半の水平座標は前半の全水平次数を加えたもの（BF §1.5.4）。
方針：後半の接頭水平辺数と前半の水平辺総数を使う。
規約：後半の第零頂点は共有切断頂点。
使われ方：後続成分の元の外側の置換添字を復元する。 -/
lemma append_horizontal_back {p q r s : ℕ} (a : ShufflePath p q) (b : ShufflePath r s)
    (k : Fin (r + s + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append a b).horizontal ⟨p + q + k.val, by have := k.isLt; omega⟩).val =
      p + (b.horizontal k).val := by
  change ((_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin a.val b.val (by omega)).filter
    (fun i => i.val < p + q + k.val)).card =
      p + (b.val.filter (fun i => i.val < k.val)).card
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin_prefix_card_back _ _ _ k.val (by have := k.isLt; omega), a.property]

/-- 概要：連結経路の後半の垂直座標は前半の全垂直次数を加えたもの（BF §1.5.4）。
方針：補集合の連結と後半の接頭辺数を使う。
規約：後半の最後の頂点も含む。
使われ方：後続成分の元の内側の置換添字を復元する。 -/
lemma append_vertical_back {p q r s : ℕ} (a : ShufflePath p q) (b : ShufflePath r s)
    (k : Fin (r + s + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append a b).vertical ⟨p + q + k.val, by have := k.isLt; omega⟩).val =
      q + (b.vertical k).val := by
  change ((_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin a.val b.val (by omega))ᶜ.filter
    (fun i => i.val < p + q + k.val)).card =
      q + (b.valᶜ.filter (fun i => i.val < k.val)).card
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin_compl, _root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin_prefix_card_back _ _ _ k.val (by have := k.isLt; omega),
    a.compl_card]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath

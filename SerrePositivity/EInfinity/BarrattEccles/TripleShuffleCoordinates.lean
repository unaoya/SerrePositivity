module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleFlags
public import SerrePositivity.EInfinity.BarrattEccles.OrderedSubsetPrefix
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCastCoordinates

/-!
# 三入力の shuffle の三つの座標の保存

概要：Berger–Fresse §1.1.3 の三入力の添字替えが各入力の頂点番号を保存することを示す。
方針：最初の色と最初の二色の辺集合の接頭濃度を計算し、座標の和の公式を使う。
規約：全頂点の次数の括弧は Fin.cast によって同定する。
使われ方：二通りの shuffle 合成の単体を頂点ごとに比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：三入力の添字替えは最初の入力の頂点番号を保つ（Berger–Fresse §1.1.3）。
方針：最初の色の辺集合の式と昇順部分集合の接頭濃度の公式を使う。
規約：左括弧の二つの水平座標と右括弧の最初の水平座標を比較する。
使われ方：三入力の合成単体の最初の入力の頂点を同定する。 -/
lemma tripleShuffle_first_coordinate (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (k : Fin (p + q + r + 1)) :
    v.2.horizontal (v.1.horizontal k) =
      (tripleShuffleEquiv p q r v).1.horizontal
        (Fin.cast (by omega : p + q + r + 1 = p + (q + r) + 1) k) := by
  apply Fin.ext
  change (v.2.val.filter (fun a => a.val < (v.1.val.filter (fun x => x.val < k.val)).card)).card =
    ((tripleShuffleEquiv p q r v).1.val.filter (fun x => x.val < k.val)).card
  rw [tripleShuffle_firstEdges, card_filter_finCongr, orderedSubsetEquiv_prefix_card]

/-- 概要：最初の二色の接頭辺数は添字替え後の最初と二番目の座標の和である（Berger–Fresse §1.1.3）。
方針：旗の大きい辺集合を互いに素な二色へ分け、それぞれの接頭濃度を計算する。
規約：出力の式は自然数の座標の和で述べる。
使われ方：二番目と三番目の頂点番号の保存を座標の和から導く。 -/
lemma tripleShuffle_firstTwo_prefix (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (k : Fin (p + q + r + 1)) :
    (v.1.horizontal k).val =
      ((tripleShuffleEquiv p q r v).1.horizontal
        (Fin.cast (by omega : p + q + r + 1 = p + (q + r) + 1) k)).val +
      ((tripleShuffleEquiv p q r v).2.horizontal
        ((tripleShuffleEquiv p q r v).1.vertical
          (Fin.cast (by omega : p + q + r + 1 = p + (q + r) + 1) k))).val := by
  let w := tripleShuffleEquiv p q r v
  let D := orderedSubsetEquiv w.1.valᶜ w.1.compl_card w.2.val
  have hd : Disjoint (w.1.val.filter (fun x => x.val < k.val))
      (D.val.filter (fun x => x.val < k.val)) := Finset.disjoint_left.mpr (by
    intro x hx hxD
    exact (Finset.mem_compl.mp (D.property (Finset.mem_filter.mp hxD).1))
      (Finset.mem_filter.mp hx).1)
  have hc := congrArg (fun S : Finset (Fin (p + (q + r))) =>
    (S.filter (fun x => x.val < k.val)).card) (tripleShuffle_firstTwoEdges p q r v)
  change ((w.1.val ∪ D.val).filter (fun x => x.val < k.val)).card =
    ((v.1.val.map (finCongr (Nat.add_assoc p q r)).toEmbedding).filter
      (fun x => x.val < k.val)).card at hc
  rw [Finset.filter_union, Finset.card_union_of_disjoint hd, card_filter_finCongr] at hc
  dsimp only [D] at hc
  rw [orderedSubsetEquiv_prefix_card] at hc
  exact hc.symm

/-- 概要：三入力の添字替えは二番目の入力の頂点番号を保つ（Berger–Fresse §1.1.3）。
方針：最初の座標の保存と最初の二色の接頭辺数の公式を座標の和と比較する。
規約：左括弧の垂直・水平の合成と右括弧の水平・垂直の合成を比較する。
使われ方：三入力の合成単体の二番目の入力の頂点を同定する。 -/
lemma tripleShuffle_second_coordinate (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (k : Fin (p + q + r + 1)) :
    v.2.vertical (v.1.horizontal k) =
      (tripleShuffleEquiv p q r v).2.horizontal
        ((tripleShuffleEquiv p q r v).1.vertical
          (Fin.cast (by omega : p + q + r + 1 = p + (q + r) + 1) k)) := by
  apply Fin.ext
  have h₁ := congrArg Fin.val (tripleShuffle_first_coordinate p q r v k)
  have h₂ := tripleShuffle_firstTwo_prefix p q r v k
  have h₃ := v.2.coordinate_sum (v.1.horizontal k)
  omega

/-- 概要：三入力の添字替えは三番目の入力の頂点番号を保つ（Berger–Fresse §1.1.3）。
方針：最初の二色の接頭辺数と二つの経路の座標の和を比較する。
規約：全頂点の番号は次数の移送で値を変えない。
使われ方：三入力の合成単体の三番目の入力の頂点を同定する。 -/
lemma tripleShuffle_third_coordinate (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) (k : Fin (p + q + r + 1)) :
    v.1.vertical k = (tripleShuffleEquiv p q r v).2.vertical
      ((tripleShuffleEquiv p q r v).1.vertical
        (Fin.cast (by omega : p + q + r + 1 = p + (q + r) + 1) k)) := by
  apply Fin.ext
  have h₁ := tripleShuffle_firstTwo_prefix p q r v k
  have h₂ := v.1.coordinate_sum k
  have h₃ := (tripleShuffleEquiv p q r v).1.coordinate_sum
    (Fin.cast (by omega : p + q + r + 1 = p + (q + r) + 1) k)
  have h₄ := (tripleShuffleEquiv p q r v).2.coordinate_sum
    ((tripleShuffleEquiv p q r v).1.vertical
      (Fin.cast (by omega : p + q + r + 1 = p + (q + r) + 1) k))
  simp only [Fin.val_cast] at h₃
  omega

end SerrePositivity.EInfinity.BarrattEccles

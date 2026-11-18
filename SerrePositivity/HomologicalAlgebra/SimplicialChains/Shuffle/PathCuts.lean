module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.EdgeIntervals

/-!
# AW 切断点での shuffle 経路の分割

概要：Berger–Fresse §1.1.4 の余代数適合性に使う前半・後半の shuffle 経路を構成する。
方針：水平辺集合を切断点の前後の区間へ制限する。
規約：切断点は共有頂点であり、辺は前半・後半で重ならない。
使われ方：AW と shuffle の有限和の添字を対応させる。
-/

@[expose] public section

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：切断点までの shuffle 経路（Berger–Fresse §1.1.4）。
方針：水平辺集合を始点零の接頭区間へ制限する。
規約：二次数は切断点の水平・垂直座標。
使われ方：AW 対角の前半の shuffle 項。 -/
def frontPath {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    ShufflePath (s.horizontal k).val (s.vertical k).val :=
  ⟨_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval s.val 0 ((s.horizontal k).val + (s.vertical k).val) (by
      have hc := s.coordinate_sum k
      omega), by
    rw [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_card]
    simp only [zero_le, true_and, zero_add]
    rw [s.coordinate_sum k]
    rfl⟩

/-- 概要：切断点から終点までの shuffle 経路（Berger–Fresse §1.1.4）。
方針：切断点以後の水平辺を零から番号付けし直す。
規約：二次数は p−水平座標、q−垂直座標。
使われ方：AW 対角の後半の shuffle 項。 -/
def backPath {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    ShufflePath (p - (s.horizontal k).val) (q - (s.vertical k).val) :=
  ⟨_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval s.val k.val ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (by
      have hc := s.coordinate_sum k
      have hh := (s.horizontal k).isLt
      have hv := (s.vertical k).isLt
      omega), by
    rw [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_card]
    have hc := s.coordinate_sum k
    have hh := (s.horizontal k).isLt
    have hv := (s.vertical k).isLt
    have hlen : k.val + ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) = p + q := by
      omega
    rw [hlen]
    have hsum := _root_.SerrePositivity.SimplicialChains.Shuffle.prefix_card_add_interval_card s.val k.val (p + q - k.val)
    have hk : k.val ≤ p + q := by omega
    rw [Nat.add_sub_of_le hk] at hsum
    have hfull : s.val.filter (fun i => i.val < p + q) = s.val := by
      exact Finset.filter_true_of_mem (fun i _ => i.isLt)
    rw [hfull, s.property] at hsum
    change (s.horizontal k).val +
      (s.val.filter (fun i => k.val ≤ i.val ∧ i.val < p + q)).card = p at hsum
    omega⟩

/-- 概要：前半経路の水平座標は元の水平座標（Berger–Fresse §1.1.4）。
方針：区間制限の接頭濃度公式を用いる。
規約：前半経路の頂点番号は元の経路でも同じ番号。
使われ方：前半の shuffle 単体と AW 切断を同定する。 -/
lemma frontPath_horizontal {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1))
    (i : Fin ((s.horizontal k).val + (s.vertical k).val + 1)) :
    ((_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath s k).horizontal i).val =
      (s.horizontal ⟨i.val, by have hc := s.coordinate_sum k; omega⟩).val := by
  change ((_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval s.val 0 ((s.horizontal k).val + (s.vertical k).val)
      (by have hc := s.coordinate_sum k; omega)).filter
    (fun j => j.val < i.val)).card = (s.val.filter (fun j => j.val < i.val)).card
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_prefix_card _ _ _ _ _ (by omega)]
  simp only [zero_le, true_and, zero_add]

/-- 概要：前半経路の垂直座標は元の垂直座標（Berger–Fresse §1.1.4）。
方針：水平座標の一致と二座標の和の公式から導く。
規約：座標は自然数の値で比較する。
使われ方：前半の shuffle 単体と AW 切断を同定する。 -/
lemma frontPath_vertical {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1))
    (i : Fin ((s.horizontal k).val + (s.vertical k).val + 1)) :
    ((_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath s k).vertical i).val =
      (s.vertical ⟨i.val, by have hc := s.coordinate_sum k; omega⟩).val := by
  have hfront := (_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath s k).coordinate_sum i
  have horig := s.coordinate_sum ⟨i.val, by have hc := s.coordinate_sum k; omega⟩
  have hh := _root_.SerrePositivity.SimplicialChains.Shuffle.frontPath_horizontal s k i
  dsimp only at horig
  omega

/-- 概要：後半経路の水平座標は切断点からの水平増分（Berger–Fresse §1.1.4）。
方針：元の水平辺の接頭濃度を前半と後半へ分割する。
規約：後半の頂点 i は元の頂点 k+i に対応する。
使われ方：後半の shuffle 単体と AW 切断を同定する。 -/
lemma backPath_horizontal {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1))
    (i : Fin ((p - (s.horizontal k).val) + (q - (s.vertical k).val) + 1)) :
    (s.horizontal k).val + ((_root_.SerrePositivity.SimplicialChains.Shuffle.backPath s k).horizontal i).val =
      (s.horizontal ⟨k.val + i.val, by
        have hc := s.coordinate_sum k
        omega⟩).val := by
  change (s.horizontal k).val +
    ((_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval s.val k.val ((p - (s.horizontal k).val) + (q - (s.vertical k).val))
      (by have hc := s.coordinate_sum k; omega)).filter
      (fun j => j.val < i.val)).card = (s.val.filter (fun j => j.val < k.val + i.val)).card
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeInterval_prefix_card _ _ _ _ _ (by omega)]
  exact _root_.SerrePositivity.SimplicialChains.Shuffle.prefix_card_add_interval_card s.val k.val i.val

/-- 概要：後半経路の垂直座標は切断点からの垂直増分（Berger–Fresse §1.1.4）。
方針：水平増分と二座標の和の公式から導く。
規約：自然数の和として差を表し切り捨て減算を避ける。
使われ方：後半の shuffle 単体と AW 切断を同定する。 -/
lemma backPath_vertical {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1))
    (i : Fin ((p - (s.horizontal k).val) + (q - (s.vertical k).val) + 1)) :
    (s.vertical k).val + ((_root_.SerrePositivity.SimplicialChains.Shuffle.backPath s k).vertical i).val =
      (s.vertical ⟨k.val + i.val, by
        have hc := s.coordinate_sum k
        omega⟩).val := by
  have hback := (_root_.SerrePositivity.SimplicialChains.Shuffle.backPath s k).coordinate_sum i
  have horig := s.coordinate_sum ⟨k.val + i.val, by
    have hc := s.coordinate_sum k
    have hh := (s.horizontal k).isLt
    have hv := (s.vertical k).isLt
    omega⟩
  have hcut := s.coordinate_sum k
  have hh := _root_.SerrePositivity.SimplicialChains.Shuffle.backPath_horizontal s k i
  dsimp only at horig
  omega

end SerrePositivity.SimplicialChains.Shuffle

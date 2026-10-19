module

public import SerrePositivity.EInfinity.Shuffle.EdgeJoin
public import SerrePositivity.EInfinity.Shuffle.PathCuts

/-!
# shuffle 経路の分割と連結の全単射

概要：Berger–Fresse §1.1.4 の切断付き経路を前半・後半経路の対に対応させる。
方針：水平・垂直の切断座標を記録し、辺集合の連結で経路を復元する。
規約：零次数と始端・終端での切断も同じ型で扱う。
使われ方：AW と shuffle の有限和の添字替え。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Shuffle

open BarrattEccles

/-- 概要：二つの入力の切断座標と前半・後半の経路（Berger–Fresse §1.1.4）。
方針：切断座標を有限順序の元として記録し、対応する二経路を組にする。
規約：二座標は独立であり、その和が出力の切断点。
使われ方：AW と shuffle の添字替えの分割側の添字。 -/
abbrev PathCutData (p q : ℕ) :=
  Σ r : Fin (p + 1), Σ t : Fin (q + 1),
    ShufflePath r.val t.val × ShufflePath (p - r.val) (q - t.val)

/-- 概要：切断付き shuffle 経路の分割データ（Berger–Fresse §1.1.4）。
方針：経路の切断座標と前半・後半の経路を束ねる。
規約：二つの経路は切断点の頂点を共有する。
使われ方：分割の全単射の順方向。 -/
def splitPath {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) : PathCutData p q :=
  ⟨s.horizontal k, s.vertical k, frontPath s k, backPath s k⟩

/-- 概要：分割データから復元した shuffle 経路（Berger–Fresse §1.1.4）。
方針：前半と後半の水平辺集合を連結し、濃度を加える。
規約：全二次数は元の p,q に戻る。
使われ方：分割の全単射の逆方向の経路。 -/
def joinPath {p q : ℕ} (d : PathCutData p q) : ShufflePath p q :=
  ⟨edgeJoin d.2.2.1.val d.2.2.2.val (by omega), by
    rw [edgeJoin_card, d.2.2.1.property, d.2.2.2.property]
    omega⟩

/-- 概要：分割データの出力の切断頂点（Berger–Fresse §1.1.4）。
方針：二つの入力の切断座標を足す。
規約：始端零と終端 p+q を含む。
使われ方：分割の全単射の逆方向の切断点。 -/
def cutVertex {p q : ℕ} (d : PathCutData p q) : Fin (p + q + 1) :=
  ⟨d.1.val + d.2.1.val, by omega⟩

/-- 概要：切断して連結すると元の shuffle 経路（Berger–Fresse §1.1.4）。
方針：二座標の和を切断頂点の番号へ同定し、区間制限の逆性を使う。
規約：全ての切断点で成立する。
使われ方：分割の全単射の左逆性。 -/
@[simp] lemma joinPath_splitPath {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    joinPath (splitPath s k) = s := by
  apply Subtype.ext
  change edgeJoin
      (edgeInterval s.val 0 ((s.horizontal k).val + (s.vertical k).val) (by omega))
      (edgeInterval s.val k.val ((p - (s.horizontal k).val) + (q - (s.vertical k).val))
        (by have hc := s.coordinate_sum k; omega)) (by omega) = s.val
  rw [← edgeInterval_start_eq s.val (s.coordinate_sum k)
    ((p - (s.horizontal k).val) + (q - (s.vertical k).val)) (by omega)
    (by have hc := s.coordinate_sum k; omega)]
  exact edgeJoin_edgeIntervals s.val _ _ _

/-- 概要：分割データからの連結は指定された水平切断座標を持つ（Berger–Fresse §1.1.4）。
方針：切断点より前の水平辺の濃度を前半の辺集合へ戻す。
規約：第一座標は Fin(p+1) の等式として述べる。
使われ方：分割の全単射の右逆性。 -/
@[simp] lemma joinPath_horizontal_cut {p q : ℕ} (d : PathCutData p q) :
    (joinPath d).horizontal (cutVertex d) = d.1 := by
  apply Fin.ext
  change ((joinPath d).val.filter (fun i => i.val < d.1.val + d.2.1.val)).card = d.1.val
  have he := edgeInterval_card (joinPath d).val 0 (d.1.val + d.2.1.val) (by omega)
  simp only [zero_le, true_and, zero_add] at he
  rw [← he]
  change (edgeInterval (edgeJoin d.2.2.1.val d.2.2.2.val (by omega))
    0 (d.1.val + d.2.1.val) (by omega)).card = d.1.val
  rw [edgeInterval_edgeJoin_front]
  exact d.2.2.1.property

/-- 概要：分割データからの連結は指定された垂直切断座標を持つ（Berger–Fresse §1.1.4）。
方針：水平切断座標と二座標の和の公式から導く。
規約：第二座標は Fin(q+1) の等式として述べる。
使われ方：分割の全単射の右逆性。 -/
@[simp] lemma joinPath_vertical_cut {p q : ℕ} (d : PathCutData p q) :
    (joinPath d).vertical (cutVertex d) = d.2.1 := by
  apply Fin.ext
  have hc := (joinPath d).coordinate_sum (cutVertex d)
  rw [joinPath_horizontal_cut] at hc
  change d.1.val + ((joinPath d).vertical (cutVertex d)).val = d.1.val + d.2.1.val at hc
  omega

end SerrePositivity.EInfinity.Shuffle

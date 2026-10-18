module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleCornerPartition

/-!
# 次数0の入力に対応する経路の向き

概要：Berger–Fresse §1.1.3 の片方の入力が次数0の場合の shuffle 経路を扱う。
方針：水平次数0では水平辺集合が空、垂直次数0では補集合が空となることを使う。
規約：次数0の方向の辺や同方向の角は存在しない。
使われ方：次数0の場合の全境界の分割から存在しない方向の寄与を取り除く。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：水平次数0の経路に水平辺はない（Berger–Fresse §1.1.3）。
方針：水平辺集合の濃度が零なので空集合である。
規約：任意の辺番号について述べる。
使われ方：水平始端・終端・内部角の添字が空であることを示す。 -/
lemma ShufflePath.notMem_leftZero {q : ℕ} (s : ShufflePath 0 q) (a : Fin (0 + q)) :
    a ∉ s.val := by
  rw [Finset.card_eq_zero.mp s.property]
  exact Finset.notMem_empty a

/-- 概要：垂直次数0の経路の全ての辺は水平である（Berger–Fresse §1.1.3）。
方針：水平辺集合の補集合の濃度が零なので空集合である。
規約：任意の辺番号について述べる。
使われ方：垂直始端・終端・内部角の添字が空であることを示す。 -/
lemma ShufflePath.mem_rightZero {p : ℕ} (s : ShufflePath p 0) (a : Fin (p + 0)) :
    a ∈ s.val := by
  by_contra ha
  have hc := Finset.mem_compl.mpr ha
  rw [Finset.card_eq_zero.mp s.compl_card] at hc
  exact Finset.notMem_empty a hc

/-- 概要：水平次数0の shuffle 経路は一意である（Berger–Fresse §1.1.3）。
方針：全ての辺が水平辺集合に属さないことから集合を比較する。
規約：空の経路も含む。
使われ方：次数0の入力に対する shuffle の一意性を与える。 -/
lemma ShufflePath.leftZero_unique {q : ℕ} (s t : ShufflePath 0 q) : s = t := by
  apply Subtype.ext
  ext a
  exact iff_of_false (s.notMem_leftZero a) (t.notMem_leftZero a)

/-- 概要：垂直次数0の shuffle 経路は一意である（Berger–Fresse §1.1.3）。
方針：全ての辺が水平辺集合に属することから集合を比較する。
規約：空の経路も含む。
使われ方：次数0の入力に対する shuffle の一意性を与える。 -/
lemma ShufflePath.rightZero_unique {p : ℕ} (s t : ShufflePath p 0) : s = t := by
  apply Subtype.ext
  ext a
  exact iff_of_true (s.mem_rightZero a) (t.mem_rightZero a)

/-- 概要：水平次数0の経路に水平な隣接角は存在しない（Berger–Fresse §1.1.3）。
方針：最初の辺が水平であるという条件を空の水平辺集合と矛盾させる。
規約：角の添字型が空であることを型クラスとして返す。
使われ方：水平な内部境界和を零にする。 -/
lemma isEmpty_horizontalAdjacentCorner_leftZero (q : ℕ) :
    IsEmpty (HorizontalAdjacentCorner 0 q) :=
  ⟨fun c => c.val.1.notMem_leftZero c.val.2.1 c.property.2.1⟩

/-- 概要：垂直次数0の経路に垂直な隣接角は存在しない（Berger–Fresse §1.1.3）。
方針：最初の辺が垂直であるという条件を全ての辺が水平であることと矛盾させる。
規約：角の添字型が空であることを型クラスとして返す。
使われ方：垂直な内部境界和を零にする。 -/
lemma isEmpty_verticalAdjacentCorner_rightZero (p : ℕ) :
    IsEmpty (VerticalAdjacentCorner p 0) :=
  ⟨fun c => c.property.2.1 (c.val.1.mem_rightZero c.val.2.1)⟩

end SerrePositivity.EInfinity.BarrattEccles

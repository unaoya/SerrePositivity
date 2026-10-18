module

public import SerrePositivity.EInfinity.BarrattEccles.ShuffleZeroDirections
public import SerrePositivity.EInfinity.BarrattEccles.ShufflePermutationCharacterization

/-!
# 一方の次数が0の標準 shuffle 経路

概要：Berger–Fresse §1.1.3 の単位則で使う、水平または垂直だけからなる経路を計算する。
方針：空集合と全辺集合の経路を選び、置換の二ブロックの特徴づけで signature を求める。
規約：次数0の側に辺はなく、shuffle の符号は1である。
使われ方：単位単体との shuffle 和を一項に簡約する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：水平辺がない標準経路（Berger–Fresse §1.1.3）。
方針：水平辺集合として空集合を取る。
規約：水平次数は0、垂直次数は q である。
使われ方：左の入力が次数0の shuffle 和の唯一の添字となる。 -/
def zeroLeftPath (q : ℕ) : ShufflePath 0 q := ⟨∅, rfl⟩

/-- 概要：全ての辺が水平である標準経路（Berger–Fresse §1.1.3）。
方針：水平辺集合として全辺集合を取る。
規約：水平次数は p、垂直次数は0である。
使われ方：右の入力が次数0の shuffle 和の唯一の添字となる。 -/
def zeroRightPath (p : ℕ) : ShufflePath p 0 := ⟨Finset.univ, by simp⟩

/-- 概要：水平次数0の shuffle 置換は恒等である（Berger–Fresse §1.1.3）。
方針：二ブロックの単調性と、水平辺集合が空であることによる置換の特徴づけを使う。
規約：経路は一意なので標準経路に制限しない。
使われ方：左側の次数0の shuffle の signature を計算する。 -/
lemma ShufflePath.permutation_leftZero {q : ℕ} (s : ShufflePath 0 q) : s.permutation = 1 := by
  symm
  apply s.permutation_eq_of_blocks
  · intro x hx y hy hxy; exact hxy
  · intro x hx y hy hxy; exact hxy
  · intro x
    exact iff_of_false (s.notMem_leftZero x) (by omega)

/-- 概要：垂直次数0の shuffle 置換は恒等である（Berger–Fresse §1.1.3）。
方針：二ブロックの単調性と、水平辺集合が全体であることによる特徴づけを使う。
規約：経路は一意なので標準経路に制限しない。
使われ方：右側の次数0の shuffle の signature を計算する。 -/
lemma ShufflePath.permutation_rightZero {p : ℕ} (s : ShufflePath p 0) : s.permutation = 1 := by
  symm
  apply s.permutation_eq_of_blocks
  · intro x hx y hy hxy; exact hxy
  · intro x hx y hy hxy; exact hxy
  · intro x
    exact iff_of_true (s.mem_rightZero x) (by have h := x.isLt; omega)

/-- 概要：水平次数0の shuffle の符号は1である（Berger–Fresse §1.1.3）。
方針：shuffle 置換が恒等であることを signature へ送る。
規約：符号は整数の単元である。
使われ方：左側の次数0の shuffle 和の係数を簡約する。 -/
@[simp] lemma ShufflePath.sign_leftZero {q : ℕ} (s : ShufflePath 0 q) : s.sign = 1 := by
  simp only [ShufflePath.sign, s.permutation_leftZero, map_one]

/-- 概要：垂直次数0の shuffle の符号は1である（Berger–Fresse §1.1.3）。
方針：shuffle 置換が恒等であることを signature へ送る。
規約：符号は整数の単元である。
使われ方：右側の次数0の shuffle 和の係数を簡約する。 -/
@[simp] lemma ShufflePath.sign_rightZero {p : ℕ} (s : ShufflePath p 0) : s.sign = 1 := by
  simp only [ShufflePath.sign, s.permutation_rightZero, map_one]

/-- 概要：垂直次数0の経路の水平座標は頂点番号に一致する（Berger–Fresse §1.1.3）。
方針：垂直座標が零であることと座標の和の公式を使う。
規約：次数 p+0+1 と p+1 は定義上同じである。
使われ方：右の単位単体との shuffle の頂点を計算する。 -/
lemma ShufflePath.horizontal_rightZero {p : ℕ} (s : ShufflePath p 0)
    (k : Fin (p + 0 + 1)) : s.horizontal k = k := by
  apply Fin.ext
  have h := s.coordinate_sum k
  have hv : (s.vertical k).val = 0 := congrArg Fin.val (Fin.eq_zero (s.vertical k))
  omega

/-- 概要：水平次数0の経路の垂直座標の値は頂点番号に一致する（Berger–Fresse §1.1.3）。
方針：水平座標が零であることと座標の和の公式を使う。
規約：次数の括弧を跨ぐため自然数としての値で述べる。
使われ方：左の単位単体との shuffle の頂点を計算する。 -/
lemma ShufflePath.vertical_leftZero_val {q : ℕ} (s : ShufflePath 0 q)
    (k : Fin (0 + q + 1)) : (s.vertical k).val = k.val := by
  have h := s.coordinate_sum k
  have hh : (s.horizontal k).val = 0 := congrArg Fin.val (Fin.eq_zero (s.horizontal k))
  omega

end SerrePositivity.EInfinity.BarrattEccles

module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.JoinInversions
public import SerrePositivity.EInfinity.BarrattEccles.ShufflePathCast
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleZeroPaths

/-!
模型。文献の定義との比較は後で
# 成分次数から経路を連結する

概要：Berger–Fresse §1.5.4–6 の成分の水平・垂直移動を実際の shuffle 経路へ組み立てる。
方針：辺集合を連結し、既存の逆転数の公式から連結の符号を計算する。
規約：水平次数は外側、垂直次数は内側。
使われ方：合成語の成分次数から d×e の経路を構成する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.SimplicialChains.Shuffle

/-- 概要：水平にだけ進む経路（BF §1.5.4）。
方針：全ての辺を水平とする。
規約：零辺の経路も含む。
使われ方：外側の一成分の移動を表す。 -/
def horizontal (p : ℕ) : ShufflePath p 0 := ⟨Finset.univ, by simp⟩

/-- 概要：垂直にだけ進む経路（BF §1.5.4）。
方針：水平辺集合を空にする。
規約：零辺の経路も含む。
使われ方：内側の一成分の移動を表す。 -/
def vertical (q : ℕ) : ShufflePath 0 q := ⟨∅, rfl⟩

/-- 概要：二つの経路を成分の順序で連結（BF §1.5.4）。
方針：辺集合の既存の連結を使い、水平辺数を加える。
規約：総水平・垂直次数は各入力の和。
使われ方：任意個の成分移動を一つの shuffle 経路へまとめる。 -/
def append {p q r s : ℕ} (a : ShufflePath p q) (b : ShufflePath r s) :
    ShufflePath (p + r) (q + s) :=
  ⟨_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin a.val b.val (by omega), by rw [_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin_card, a.property, b.property]⟩

/-- 概要：経路連結の符号は前半垂直次数×後半水平次数の Koszul 符号を持つ（BF §1.5.6）。
方針：辺集合の逆転数の加法公式を (−1) の冪へ移す。
規約：符号は整数の単元。
使われ方：成分移動の経路の符号を次数の積から求める。 -/
lemma append_sign {p q r s : ℕ} (a : ShufflePath p q) (b : ShufflePath r s) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append a b).sign = (-1 : ℤˣ) ^ (q * r) * a.sign * b.sign := by
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.sign_eq_pow_inversionNumber]
  change (-1 : ℤˣ) ^ _root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin a.val b.val (by omega)) = _
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber_edgeJoin, a.property, b.property, Nat.add_sub_cancel_left,
    pow_add, pow_add]
  ac_rfl

/-- 概要：内側成分の移動の後に外側成分の移動を置く経路（BF §1.5.4）。
方針：垂直だけの経路と水平だけの経路を連結する。
規約：順序は垂直、水平。
使われ方：一出現での内側成分とその後の外側成分の移動を表す。 -/
def corner (h v : ℕ) : ShufflePath h v :=
  shufflePathCastEquiv (Nat.zero_add h) (Nat.add_zero v) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.vertical v) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.horizontal h))

/-- 概要：垂直から水平への一成分の折れ曲がりの符号（BF §1.5.6）。
方針：純粋な二経路の符号は 1 なので交差符号だけが残る。
規約：零次数の成分も含む。
使われ方：全成分の経路の符号を帰納的に計算する。 -/
@[simp] lemma corner_sign (h v : ℕ) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.corner h v).sign = (-1 : ℤˣ) ^ (v * h) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.corner, shufflePathCastEquiv_sign, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath.append_sign, ShufflePath.sign_leftZero,
    ShufflePath.sign_rightZero, mul_one, mul_one]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreePath

module

public import SerrePositivity.EInfinity.BarrattEccles.TripleShufflePermutation
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleExchangePermutation
public import SerrePositivity.EInfinity.BarrattEccles.ShufflePathCast

/-!
# 並列の二段の shuffle の添字と符号

概要：Berger–Fresse §1.1.3 の異なる二つの入力への代入順序を交換する。
方針：三入力を右括弧へ移し、内側の二方向を交換して左括弧へ戻す。
規約：第一入力の次数 p を保ち、第二・第三入力の次数 q,r を交換する。
使われ方：並列結合則の二重有限和の添字替えと Koszul 符号を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：第二・第三入力を交換する二段の shuffle の添字の全単射（Berger–Fresse §1.1.3）。
方針：三入力の括弧の変更と内側の経路の方向交換を合成する。
規約：左の添字は ((p,q),r)、右の添字は ((p,r),q) を表す。
使われ方：並列結合則で代入順序の異なる二重和を対応させる。 -/
def parallelShuffleEquiv (p q r : ℕ) :
    ShufflePath (p + q) r × ShufflePath p q ≃
      ShufflePath (p + r) q × ShufflePath p r :=
  (tripleShuffleEquiv p q r).trans
    ((Equiv.prodCongr (shufflePathCastEquiv (rfl : p = p) (Nat.add_comm q r))
      (shuffleExchangeEquiv q r)).trans (tripleShuffleEquiv p r q).symm)

/-- 概要：並列の添字替えを右括弧へ移すと内側の方向交換になる（Berger–Fresse §1.1.3）。
方針：最後の三入力の全単射とその逆を打ち消す。
規約：外側の内側辺数 q+r は r+q へ移送する。
使われ方：並列の添字替えの座標と符号を計算する。 -/
lemma rightTriple_parallelShuffleEquiv (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    tripleShuffleEquiv p r q (parallelShuffleEquiv p q r v) =
      (shufflePathCastEquiv (rfl : p = p) (Nat.add_comm q r)
        (tripleShuffleEquiv p q r v).1, (tripleShuffleEquiv p q r v).2.exchange) :=
  (tripleShuffleEquiv p r q).apply_symm_apply _

/-- 概要：並列の shuffle の添字替えは符号の積を (−1)^(qr) 倍する（Berger–Fresse §1.1.3）。
方針：三入力の符号の結合則を二回使い、内側の方向交換の符号を掛ける。
規約：q,r は交換する二つの入力の鎖次数である。
使われ方：並列の代入順序を交換した二重 shuffle 和の係数を同定する。 -/
lemma parallelShuffle_sign (p q r : ℕ)
    (v : ShufflePath (p + q) r × ShufflePath p q) :
    (parallelShuffleEquiv p q r v).1.sign * (parallelShuffleEquiv p q r v).2.sign =
      (-1 : ℤˣ) ^ (q * r) * (v.1.sign * v.2.sign) := by
  have hL := tripleShuffle_sign p q r v
  have hR := tripleShuffle_sign p r q (parallelShuffleEquiv p q r v)
  rw [rightTriple_parallelShuffleEquiv] at hR
  simp only [shufflePathCastEquiv_sign, ShufflePath.exchange_sign] at hR
  calc
    (parallelShuffleEquiv p q r v).1.sign * (parallelShuffleEquiv p q r v).2.sign =
        (tripleShuffleEquiv p q r v).1.sign *
          ((-1 : ℤˣ) ^ (q * r) * (tripleShuffleEquiv p q r v).2.sign) := hR
    _ = (-1 : ℤˣ) ^ (q * r) *
        ((tripleShuffleEquiv p q r v).1.sign * (tripleShuffleEquiv p q r v).2.sign) := by ac_rfl
    _ = (-1 : ℤˣ) ^ (q * r) * (v.1.sign * v.2.sign) := by rw [← hL]

end SerrePositivity.EInfinity.BarrattEccles

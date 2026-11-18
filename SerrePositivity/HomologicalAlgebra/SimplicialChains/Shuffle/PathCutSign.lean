module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.PathCutEquiv
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.JoinInversions

/-!
# shuffle の切断と Koszul 符号

概要：Berger–Fresse §1.1.4 の切断で生じる符号を計算する。
方針：連結の逆転数の加法公式に前半・後半の水平辺数を代入する。
規約：交差符号は前半の垂直次数と後半の水平次数の積で決まる。
使われ方：AW と shuffle の余代数適合性の有限和。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：経路の連結の符号は二経路の符号と交差符号の積（BF §1.1.4）。
方針：逆転数の和を (−1) の冪の積へ変換する。
規約：整数の単元の等式として述べる。
使われ方：経路を切断したときの Koszul 符号。 -/
lemma joinPath_sign {p q : ℕ} (d : _root_.SerrePositivity.SimplicialChains.Shuffle.PathCutData p q) :
    (_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath d).sign = (-1 : ℤˣ) ^ (d.2.1.val * (p - d.1.val)) *
      d.2.2.1.sign * d.2.2.2.sign := by
  simp only [_root_.SerrePositivity.SimplicialChains.Shuffle.sign_eq_pow_inversionNumber]
  change (-1 : ℤˣ) ^ _root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber (_root_.SerrePositivity.SimplicialChains.Shuffle.edgeJoin d.2.2.1.val d.2.2.2.val (by omega)) = _
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.inversionNumber_edgeJoin, d.2.2.1.property, d.2.2.2.property,
    Nat.add_sub_cancel_left, pow_add, pow_add]
  ac_rfl

/-- 概要：切断の符号は前半垂直次数と後半水平次数の Koszul 符号（BF §1.1.4）。
方針：切断データの連結の符号を、元の経路との一致で戻す。
規約：始端・終端を含む全ての切断点で成立する。
使われ方：shuffle の項別の AW 公式を符号付き和へ拡張する。 -/
lemma pathCut_sign {p q : ℕ} (s : ShufflePath p q) (k : Fin (p + q + 1)) :
    s.sign = (-1 : ℤˣ) ^ ((s.vertical k).val * (p - (s.horizontal k).val)) *
      (_root_.SerrePositivity.SimplicialChains.Shuffle.frontPath s k).sign * (_root_.SerrePositivity.SimplicialChains.Shuffle.backPath s k).sign := by
  have he := _root_.SerrePositivity.SimplicialChains.Shuffle.joinPath_sign (_root_.SerrePositivity.SimplicialChains.Shuffle.splitPath s k)
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath_splitPath] at he
  simpa only [_root_.SerrePositivity.SimplicialChains.Shuffle.splitPath] using he

end SerrePositivity.SimplicialChains.Shuffle

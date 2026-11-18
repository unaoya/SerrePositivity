module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.PathCutSign

/-!
# 切断付き shuffle 和の添字替え

概要：Berger–Fresse §1.1.4 の経路分割と符号公式を有限和へ移す。
方針：分割の全単射で添字を替え、連結経路の signature を分解する。
規約：値域は任意の可換加法群であり、符号は整数のスカラー作用として扱う。
使われ方：AW と shuffle の項別公式から余代数適合性の有限和を比較する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.SerrePositivity.EInfinity.BarrattEccles

variable {M : Type*} [AddCommGroup M]

/-- 概要：切断付き経路上の和を分割データ上の和へ替える（BF §1.1.4）。
方針：経路分割の全単射で有限和を移す。
規約：切断点の両端も和に含める。
使われ方：shuffle の全ての AW 成分を同時に比較する。 -/
lemma sum_pathCut {p q : ℕ} (f : ShufflePath p q → Fin (p + q + 1) → M) :
    (∑ s, ∑ k, f s k) = ∑ d : _root_.SerrePositivity.SimplicialChains.Shuffle.PathCutData p q, f (_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath d) (_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d) := by
  rw [← Fintype.sum_prod_type (f := fun v => f v.1 v.2)]
  apply Fintype.sum_equiv (_root_.SerrePositivity.SimplicialChains.Shuffle.pathCutEquiv p q)
  intro v
  have h := (_root_.SerrePositivity.SimplicialChains.Shuffle.pathCutEquiv p q).left_inv v
  exact congrArg (fun w => f w.1 w.2) h.symm

/-- 概要：符号付き切断和を前後経路の符号と Koszul 符号で書く（BF §1.1.4）。
方針：添字替えの後で連結の符号を整数の等式へ移す。
規約：前半の垂直次数と後半の水平次数を交換する符号を明示する。
使われ方：AW と shuffle の余代数適合性の有限和の符号比較。 -/
lemma signed_sum_pathCut {p q : ℕ} (f : ShufflePath p q → Fin (p + q + 1) → M) :
    (∑ s, ∑ k, (s.sign : ℤ) • f s k) =
      ∑ d : _root_.SerrePositivity.SimplicialChains.Shuffle.PathCutData p q,
        ((-1 : ℤ) ^ (d.2.1.val * (p - d.1.val)) *
          (d.2.2.1.sign : ℤ) * (d.2.2.2.sign : ℤ)) • f (_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath d) (_root_.SerrePositivity.SimplicialChains.Shuffle.cutVertex d) := by
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.sum_pathCut]
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  have he := congrArg (fun s : ℤˣ => (s : ℤ)) (_root_.SerrePositivity.SimplicialChains.Shuffle.joinPath_sign d)
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using he

end SerrePositivity.SimplicialChains.Shuffle

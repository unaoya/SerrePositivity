module

public import SerrePositivity.EInfinity.BarrattEccles.Normalized

/-!
# Barratt–Eccles 複体の次数規約

概要：Berger–Fresse §1.1 の鎖次数と本リポジトリのコチェイン次数の対応を明示する。
方針：自然数次数の正規化鎖から整数次数への零拡張の同型を用いる。
規約：鎖次数 q はコチェイン次数 −q に対応する。
使われ方：E(n) の基底と微分を正規化鎖の次数ごとに扱う。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：E(n) の次数 −q は正規化 Moore 鎖の次数 q である（Berger–Fresse §1.1）。
方針：次数埋め込みによる延長の標準同型を使う。
規約：加群圏の同型として表す。
使われ方：正規化鎖の成分の議論を E(n) に移す。 -/
def complexXIso (n q : ℕ) :
    (complex A n).X (-(q : ℤ)) ≅
      ((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
        ((linearization A).obj (simplicial n))).X q :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat rfl

/-- 概要：E(n) の正次数の成分は零対象である（Berger–Fresse §1.1）。
方針：正整数が q ↦ −q の像にないことを使う。
規約：正次数とはコチェイン次数が厳密に正であること。
使われ方：E(n) の非正次数への集中を与える。 -/
lemma complex_isZero_positive (n : ℕ) (k : ℤ) (hk : 0 < k) :
    Limits.IsZero ((complex A n).X k) := by
  apply HomologicalComplex.isZero_extend_X
  intro q
  change -(q : ℤ) ≠ k
  omega

end SerrePositivity.EInfinity.BarrattEccles

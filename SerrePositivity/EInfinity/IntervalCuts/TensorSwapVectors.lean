module

public import SerrePositivity.EInfinity.IntervalCuts.TensorFirstSwap
public import SerrePositivity.EInfinity.IntervalCuts.CutRenaming
public import SerrePositivity.CategoryTheory.Monoidal.AdjacentTranspositions
public import SerrePositivity.GroupTheory.Coxeter.FirstToLast

/-!
# 区間の面テンソルの隣接交換

概要：Berger–Fresse §2.2.4 の隣接因子交換を実際の区間生成元で評価する。
方針：先頭の面の挿入と二因子交換の公式を右括弧テンソルへ適用する。
規約：任意の指定整数次数を保ち、次数証明による移送を明示する。
使われ方：区間切断の置換等変性に必要な出力側の Koszul 公式。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：先頭面を挿入した族の全次数（BF §2.2.3）。
方針：右括弧の再帰式を評価する。
規約：後続族の同一写像による表示を簡約する。
使われ方：隣接交換での整数次数の証明。 -/
lemma tupleDegree_cons (n : ℕ) (a : Simplex) (f : Fin n → Simplex) :
    tupleDegree (n + 1) (Fin.cons a f) = simplexDegree a + tupleDegree n f := rfl

/-- 概要：指定次数の面テンソルへの先頭挿入公式（BF §2.2.6）。
方針：一般の後続族の次数と先頭面の次数で再帰式を評価する。
規約：後続の元は自然な全次数で保持する。
使われ方：先頭二因子の交換を斉次三入力へ帰着する。 -/
lemma tensorVectorAt_cons (n : ℕ) (a : Simplex) (f : Fin n → Simplex) (r : ℤ)
    (h : -(simplexDegree a : ℤ) + -(tupleDegree n f : ℤ) = r) :
    tensorVectorAt A (n + 1) (Fin.cons a f) r
      (by simp only [tupleDegree_cons, Nat.cast_add]; omega) =
      ιTensorObj (interval A) (power (interval A) n)
        (-(simplexDegree a : ℤ)) (-(tupleDegree n f : ℤ)) r h
        (faceVector A a ⊗ₜ[A] tensorVector A n f) := by
  have h' := tensorVectorAt_succ A n (Fin.cons a f)
    (-(simplexDegree a : ℤ)) (-(tupleDegree n f : ℤ)) r rfl rfl h
  simpa only [Fin.cons_zero, Fin.cons_succ, eqToHom_refl, ModuleCat.id_apply,
    tensorVectorAt_refl] using! h'

/-- 概要：指定次数の面テンソルの先頭二因子を個別に挿入する公式（BF §2.2.6）。
方針：先頭挿入を二回適用して中間和次数を揃える。
規約：先頭二面と任意の後続族。
使われ方：実際の先頭交換公式の入力を供給する。 -/
lemma tensorVectorAt_cons_cons (n : ℕ) (a b : Simplex) (f : Fin n → Simplex) (r : ℤ)
    (h : -(simplexDegree a : ℤ) + (-(simplexDegree b : ℤ) +
      -(tupleDegree n f : ℤ)) = r) :
    tensorVectorAt A (n + 2) (Fin.cons a (Fin.cons b f)) r
      (by simp only [tupleDegree_cons, Nat.cast_add]; omega) =
      ιTensorObj (interval A) ((interval A) ⊗ power (interval A) n)
        (-(simplexDegree a : ℤ)) (-(simplexDegree b : ℤ) + -(tupleDegree n f : ℤ)) r h
        (faceVector A a ⊗ₜ[A]
          ιTensorObj (interval A) (power (interval A) n) (-(simplexDegree b : ℤ))
            (-(tupleDegree n f : ℤ)) (-(simplexDegree b : ℤ) + -(tupleDegree n f : ℤ))
            rfl (faceVector A b ⊗ₜ[A] tensorVector A n f)) := by
  rw [tensorVectorAt_succ A (n + 1) _ (-(simplexDegree a : ℤ))
    (-(simplexDegree b : ℤ) + -(tupleDegree n f : ℤ)) r rfl
    (by change -((simplexDegree b + tupleDegree n f : ℕ) : ℤ) = _; omega) h]
  simp only [Fin.cons_succ, eqToHom_refl]
  rw [tensorVectorAt_cons A n b f _ rfl]
  rfl

/-- 概要：先頭二面の交換はその二次数の Koszul 符号を持つ（BF §2.2.4）。
方針：二重の先頭挿入を実際の三入力交換公式へ渡す。
規約：全次数は元と同じ指定整数。
使われ方：隣接交換の再帰の基底。 -/
lemma swapFirstIso_tensorVectorAt (n : ℕ) (a b : Simplex) (f : Fin n → Simplex) (r : ℤ)
    (h : -(simplexDegree a : ℤ) + (-(simplexDegree b : ℤ) +
      -(tupleDegree n f : ℤ)) = r) :
    (swapFirstIso (interval A) n).hom.f r
      (tensorVectorAt A (n + 2) (Fin.cons a (Fin.cons b f)) r
        (by simp only [tupleDegree_cons, Nat.cast_add]; omega)) =
      ((-(simplexDegree a : ℤ)) * (-(simplexDegree b : ℤ))).negOnePow •
        tensorVectorAt A (n + 2) (Fin.cons b (Fin.cons a f)) r
          (by simp only [tupleDegree_cons, Nat.cast_add]; omega) := by
  rw [tensorVectorAt_cons_cons A n a b f r h,
    tensorVectorAt_cons_cons A n b a f r (by omega)]
  exact swapFirstIso_apply A n _ _ _ r h (faceVector A a) (faceVector A b) (tensorVector A n f)

end SerrePositivity.EInfinity.IntervalCuts

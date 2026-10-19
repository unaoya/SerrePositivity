module

public import SerrePositivity.EInfinity.IntervalCuts.FamilyBlocks
public import SerrePositivity.EInfinity.IntervalCuts.TensorAppend

/-!
# 実際の面テンソルの指定因子でのブロック表示

概要：Berger–Fresse §2.2.6 の外側面テンソルを前方・指定因子・後方へ分ける。
方針：族の三ブロック表示を実際の appendIso と arity 移送の評価へ渡す。
規約：整数全次数は元の指定値に保つ。
使われ方：実際の余代入のブロック評価への入力を作る。
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

/-- 概要：指定因子の前後の面テンソルの連結は元の面テンソル（BF §2.2.6）。
方針：指定因子と後方、続いて前方を実際の連結で結び、arity を元へ移す。
規約：元の指定整数全次数と前後の自然な面次数を使う。
使われ方：余代入のブロック表示へ元の出力テンソルを接続する。 -/
lemma tensorVectorAt_family_blocks {m : ℕ} (f : Fin (m + 1) → Simplex) (i : Fin (m + 1))
    (r : ℤ) (hr : -(tupleDegree (m + 1) f : ℤ) = r) :
    tensorVectorAt A (m + 1) f r hr =
      (eqToHom (congrArg (power (interval A))
        (by omega : i.val + (m - i.val + 1) = m + 1))).f r
        ((appendIso (interval A) i.val (m - i.val + 1)).hom.f r
          (ιTensorObj (power (interval A) i.val) (power (interval A) (m - i.val + 1))
            (-(tupleDegree i.val (prefixFamily f i) : ℤ))
            (-(simplexDegree (f i) : ℤ) + -(tupleDegree (m - i.val) (suffixFamily f i) : ℤ))
            r (by have := tupleDegree_family_blocks f i; omega)
            (tensorVector A i.val (prefixFamily f i) ⊗ₜ[A]
              ιTensorObj (interval A) (power (interval A) (m - i.val))
                (-(simplexDegree (f i) : ℤ)) (-(tupleDegree (m - i.val) (suffixFamily f i) : ℤ))
                (-(simplexDegree (f i) : ℤ) +
                  -(tupleDegree (m - i.val) (suffixFamily f i) : ℤ)) rfl
                (faceVector A (f i) ⊗ₜ[A] tensorVector A (m - i.val) (suffixFamily f i))))) := by
  have hs := tensorVectorAt_cons A (m - i.val) (f i) (suffixFamily f i)
    (-(simplexDegree (f i) : ℤ) + -(tupleDegree (m - i.val) (suffixFamily f i) : ℤ)) rfl
  have H := appendIso_tensorVectorAt A i.val (m - i.val + 1) (prefixFamily f i)
    (Fin.cons (f i) (suffixFamily f i)) (-(tupleDegree i.val (prefixFamily f i) : ℤ))
    (-(simplexDegree (f i) : ℤ) + -(tupleDegree (m - i.val) (suffixFamily f i) : ℤ))
    r rfl (by rw [tupleDegree_cons]; omega)
    (by have := tupleDegree_family_blocks f i; omega)
  rw [tensorVectorAt_refl, hs] at H
  rw [H]
  simpa only [← family_eq_blocks f i] using! (tensorVectorAt_arity_transport A
    (by omega : i.val + (m - i.val + 1) = m + 1)
    (Fin.append (prefixFamily f i) (Fin.cons (f i) (suffixFamily f i))) r
    (by rw [tupleDegree_append, tupleDegree_cons];
        have := tupleDegree_family_blocks f i; omega)).symm

end SerrePositivity.EInfinity.IntervalCuts

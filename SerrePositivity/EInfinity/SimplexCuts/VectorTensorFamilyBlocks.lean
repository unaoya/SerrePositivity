module

public import SerrePositivity.EInfinity.SimplexCuts.VectorTensorAppend
public import SerrePositivity.EInfinity.IntervalCuts.FamilyBlocks

/-!
# 同じ斉次テンソルの指定因子でのブロック表示

Berger–Fresse §2.2.6・§3.1、M14 L12a の既存構成の法則。
報告 §295 の元の有限族・指定整数次数・余代入を保った評価。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open IntervalCuts (prefixFamily suffixFamily insertionFamily family_eq_blocks
  insertionFamily_eq_blocks)
variable {A : Type u} [CommRing A]

/-- 同じ因子数の等式による次数和の移送（BF §2.2.6）。 -/
lemma vectorDegree_arity_transport (K : Complex A) {m n : ℕ} (h : m = n)
    (f : Fin m → Σ d : ℕ, K.X (-(d : ℤ))) :
    vectorDegree K n (f ∘ Fin.cast h.symm) = vectorDegree K m f := by
  subst n
  rfl

/-- 同じ前方・指定因子・後方の次数和（BF §2.2.6）。 -/
lemma vectorDegree_family_blocks (K : Complex A) {m : ℕ}
    (f : Fin (m + 1) → Σ d : ℕ, K.X (-(d : ℤ))) (i : Fin (m + 1)) :
    vectorDegree K (m + 1) f = vectorDegree K i.val (prefixFamily f i) +
      (f i).1 + vectorDegree K (m - i.val) (suffixFamily f i) := by
  conv_lhs => rw [family_eq_blocks f i]
  rw [vectorDegree_arity_transport K (by omega : i.val + (m - i.val + 1) = m + 1),
    vectorDegree_append, vectorDegree_cons]
  omega

/-- 同じ置換族は前方・内側・後方の次数和を持つ（BF §2.2.6）。 -/
lemma vectorDegree_insertionFamily (K : Complex A) {m n : ℕ}
    (f : Fin (m + 1) → Σ d : ℕ, K.X (-(d : ℤ)))
    (g : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (i : Fin (m + 1)) :
    vectorDegree K (m + n) (insertionFamily f g i) =
      vectorDegree K i.val (prefixFamily f i) + vectorDegree K n g +
        vectorDegree K (m - i.val) (suffixFamily f i) := by
  rw [insertionFamily_eq_blocks]
  rw [vectorDegree_arity_transport K (by omega : i.val + (n + (m - i.val)) = m + n),
    vectorDegree_append, vectorDegree_append]
  omega

/-- 概要：指定因子の前後の面テンソルの連結は元の面テンソル（BF §2.2.6）。
方針：指定因子と後方、続いて前方を実際の連結で結び、arity を元へ移す。
規約：元の指定整数全次数と前後の自然な面次数を使う。
使われ方：余代入のブロック表示へ元の出力テンソルを接続する。 -/
lemma vectorTensorAt_family_blocks (K : Complex A) {m : ℕ}
    (f : Fin (m + 1) → Σ d : ℕ, K.X (-(d : ℤ))) (i : Fin (m + 1))
    (r : ℤ) (hr : -(vectorDegree K (m + 1) f : ℤ) = r) :
    vectorTensorAt K (m + 1) f r hr =
      (eqToHom (congrArg (power K)
        (by omega : i.val + (m - i.val + 1) = m + 1))).f r
        ((appendIso K i.val (m - i.val + 1)).hom.f r
          (ιTensorObj (power K i.val) (power K (m - i.val + 1))
            (-(vectorDegree K i.val (prefixFamily f i) : ℤ))
            (-((f i).1 : ℤ) + -(vectorDegree K (m - i.val) (suffixFamily f i) : ℤ))
            r (by have := vectorDegree_family_blocks K f i; omega)
            (vectorTensor K i.val (prefixFamily f i) ⊗ₜ[A]
              ιTensorObj K (power K (m - i.val))
                (-((f i).1 : ℤ)) (-(vectorDegree K (m - i.val) (suffixFamily f i) : ℤ))
                (-((f i).1 : ℤ) +
                  -(vectorDegree K (m - i.val) (suffixFamily f i) : ℤ)) rfl
                ((f i).2 ⊗ₜ[A] vectorTensor K (m - i.val) (suffixFamily f i))))) := by
  have hs := vectorTensorAt_cons K (m - i.val) (f i) (suffixFamily f i)
    (-((f i).1 : ℤ) + -(vectorDegree K (m - i.val) (suffixFamily f i) : ℤ)) rfl
  have H := appendIso_vectorTensorAt K i.val (m - i.val + 1) (prefixFamily f i)
    (Fin.cons (f i) (suffixFamily f i)) (-(vectorDegree K i.val (prefixFamily f i) : ℤ))
    (-((f i).1 : ℤ) + -(vectorDegree K (m - i.val) (suffixFamily f i) : ℤ))
    r rfl (by rw [vectorDegree_cons]; omega)
    (by have := vectorDegree_family_blocks K f i; omega)
  rw [vectorTensorAt_refl, hs] at H
  rw [H]
  simpa only [← family_eq_blocks f i] using! (vectorTensorAt_arity_transport K
    (by omega : i.val + (m - i.val + 1) = m + 1)
    (Fin.append (prefixFamily f i) (Fin.cons (f i) (suffixFamily f i))) r
    (by rw [vectorDegree_append, vectorDegree_cons];
        have := vectorDegree_family_blocks K f i; omega)).symm


end SerrePositivity.EInfinity.SimplexCuts

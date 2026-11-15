module

public import SerrePositivity.EInfinity.SimplexCuts.VectorTensorAppend
public import SerrePositivity.EInfinity.IntervalCuts.CoInsertionBlockEvaluation

/-!
# 元の余代入を同じ斉次因子の族で評価する

Berger–Fresse §2.2.6・§3.1、M14 L12a の既存構成の法則、報告 §293。
元のparameterCrossの交換符号と二つのappendIsoを、そのまま評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]

/-- 概要：内側作用の一つの面テンソル値を余代入すると三つの面族が連結される（BF §3.1）。
方針：純粋ブロック評価に内側の指定値を代入し、二段の実際の連結を計算する。
規約：係数次数と前方次数の積の Koszul 符号、内側の整数係数を別々に保持する。
使われ方：実際の二段余演算の非零項の値と符号を評価する。 -/
lemma coInsertionBlocks_vector_apply (K C : Complex A) (s n t : ℕ)
    (θ : C ⊗ K ⟶ power K n)
    (c q z : ℤ) (f : Fin s → Σ d : ℕ, K.X (-(d : ℤ)))
    (g : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (h : Fin t → Σ d : ℕ, K.X (-(d : ℤ)))
    (hz : c + (-(vectorDegree K s f : ℤ) + (q + -(vectorDegree K t h : ℤ))) = z)
    (a : C.X c) (y : K.X q) (hg : -(vectorDegree K n g : ℤ) = c + q)
    (r : ℤ) (hθ : θ.f (c + q) (ιTensorObj C K c q (c + q) rfl (a ⊗ₜ[A] y)) =
      r • vectorTensorAt K n g (c + q) hg) :
    (IntervalCuts.coInsertionBlocks K C s n t θ).f z
      (ιTensorObj C (power K s ⊗ (K ⊗ power K t))
        c (-(vectorDegree K s f : ℤ) + (q + -(vectorDegree K t h : ℤ))) z hz
        (a ⊗ₜ[A] ιTensorObj (power K s) (K ⊗ power K t)
          (-(vectorDegree K s f : ℤ)) (q + -(vectorDegree K t h : ℤ))
          (-(vectorDegree K s f : ℤ) + (q + -(vectorDegree K t h : ℤ))) rfl
          (vectorTensor K s f ⊗ₜ[A] ιTensorObj K (power K t)
            q (-(vectorDegree K t h : ℤ)) (q + -(vectorDegree K t h : ℤ)) rfl
            (y ⊗ₜ[A] vectorTensor K t h)))) =
      (c * -(vectorDegree K s f : ℤ)).negOnePow • (r •
        vectorTensorAt K (s + (n + t)) (Fin.append f (Fin.append g h)) z (by
          rw [vectorDegree_append, vectorDegree_append]; omega)) := by
  rw [IntervalCuts.coInsertionBlocks_apply, hθ]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_zsmul]
  have hi := appendIso_vectorTensorAt K n t g h (c + q) (-(vectorDegree K t h : ℤ))
    (c + (q + -(vectorDegree K t h : ℤ))) hg rfl (by omega)
  rw [vectorTensorAt_refl] at hi
  rw [hi]
  have ho := appendIso_vectorTensorAt K s (n + t) f (Fin.append g h)
    (-(vectorDegree K s f : ℤ)) (c + (q + -(vectorDegree K t h : ℤ))) z rfl
    (by rw [vectorDegree_append]; omega) (by omega)
  rw [vectorTensorAt_refl] at ho
  rw [ho]


end SerrePositivity.EInfinity.SimplexCuts

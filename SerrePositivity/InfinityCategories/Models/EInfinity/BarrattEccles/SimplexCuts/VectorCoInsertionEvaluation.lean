module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VectorTensorAppend
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.CoInsertionBlockEvaluation

/-!
模型。文献の定義との比較は後で
# 元の余代入を同じ斉次因子の族で評価する

Berger–Fresse §2.2.6・§3.1、M14 L12a の既存構成の法則、報告 §293。
元のparameterCrossの交換符号と二つのappendIsoを、そのまま評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]

/-- 概要：内側作用の一つの面テンソル値を余代入すると三つの面族が連結される（BF §3.1）。
方針：純粋ブロック評価に内側の指定値を代入し、二段の実際の連結を計算する。
規約：係数次数と前方次数の積の Koszul 符号、内側の整数係数を別々に保持する。
使われ方：実際の二段余演算の非零項の値と符号を評価する。 -/
lemma coInsertionBlocks_vector_apply (K C : Complex A) (s n t : ℕ)
    (θ : C ⊗ K ⟶ power K n)
    (c q z : ℤ) (f : Fin s → Σ d : ℕ, K.X (-(d : ℤ)))
    (g : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (h : Fin t → Σ d : ℕ, K.X (-(d : ℤ)))
    (hz : c + (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K s f : ℤ) + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))) = z)
    (a : C.X c) (y : K.X q) (hg : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n g : ℤ) = c + q)
    (r : ℤ) (hθ : θ.f (c + q) (ιTensorObj C K c q (c + q) rfl (a ⊗ₜ[A] y)) =
      r • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K n g (c + q) hg) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coInsertionBlocks K C s n t θ).f z
      (ιTensorObj C (power K s ⊗ (K ⊗ power K t))
        c (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K s f : ℤ) + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))) z hz
        (a ⊗ₜ[A] ιTensorObj (power K s) (K ⊗ power K t)
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K s f : ℤ)) (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K s f : ℤ) + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))) rfl
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K s f ⊗ₜ[A] ιTensorObj K (power K t)
            q (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ)) (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ)) rfl
            (y ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K t h)))) =
      (c * -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K s f : ℤ)).negOnePow • (r •
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K (s + (n + t)) (Fin.append f (Fin.append g h)) z (by
          rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append]; omega)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coInsertionBlocks_apply, hθ]
  simp only [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_zsmul]
  have hi := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.appendIso_vectorTensorAt K n t g h (c + q) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))
    (c + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))) hg rfl (by omega)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_refl] at hi
  rw [hi]
  have ho := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.appendIso_vectorTensorAt K s (n + t) f (Fin.append g h)
    (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K s f : ℤ)) (c + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))) z rfl
    (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append]; omega) (by omega)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_refl] at ho
  rw [ho]


end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

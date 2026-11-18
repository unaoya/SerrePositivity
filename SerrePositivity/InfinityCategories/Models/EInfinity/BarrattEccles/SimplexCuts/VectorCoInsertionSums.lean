module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VectorCoInsertionActionEvaluation

/-!
模型。文献の定義との比較は後で
# 元のブロック余代入への斉次有限和の代入

Berger–Fresse §2.2.6・§3.1、M14 L12a の既存構成の法則、報告 §298。
元の内側の全有限和を分配し、同じappendIsoと出力順を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts (prefixFamily suffixFamily insertionFamily insertionFamily_eq_blocks
  tensorCoInsertionAction_on_blocks)
variable {A : Type u} [CommRing A]

/-- 概要：内側の符号付き面テンソル和は同じ係数の連結族の和へ移る（BF §3.1）。
方針：テンソル積と構成する複体射の加法性で分配し、各項を連結する。
規約：空和も含み、交換符号は和全体に掛ける。
使われ方：実際の内側辺余演算の非零切断和の評価。 -/
lemma coInsertionBlocks_vector_sum_apply {ι : Type v} [Fintype ι] (K C : Complex A) (s n t : ℕ)
    (θ : C ⊗ K ⟶ power K n)
    (c q z : ℤ) (f : Fin s → Σ d : ℕ, K.X (-(d : ℤ)))
    (g : ι → Fin n → Σ d : ℕ, K.X (-(d : ℤ)))
    (h : Fin t → Σ d : ℕ, K.X (-(d : ℤ)))
    (hz : c + (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K s f : ℤ) + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))) = z)
    (a : C.X c) (y : K.X q) (hg : ∀ j, -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n (g j) : ℤ) = c + q)
    (r : ι → ℤ) (hθ : θ.f (c + q) (ιTensorObj C K c q (c + q) rfl (a ⊗ₜ[A] y)) =
      ∑ j, r j • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K n (g j) (c + q) (hg j)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coInsertionBlocks K C s n t θ).f z
      (ιTensorObj C (power K s ⊗ (K ⊗ power K t))
        c (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K s f : ℤ) + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))) z hz
        (a ⊗ₜ[A] ιTensorObj (power K s) (K ⊗ power K t)
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K s f : ℤ)) (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))
          (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K s f : ℤ) + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))) rfl
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K s f ⊗ₜ[A] ιTensorObj K (power K t)
            q (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ)) (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ)) rfl
            (y ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K t h)))) =
      (c * -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K s f : ℤ)).negOnePow •
        ∑ j, r j • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K (s + (n + t)) (Fin.append f (Fin.append (g j) h)) z
          (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append]; have := hg j; omega) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.coInsertionBlocks_apply, hθ]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_zsmul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hi := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.appendIso_vectorTensorAt K n t (g j) h (c + q) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))
    (c + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))) (hg j) rfl (by omega)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_refl] at hi
  rw [hi]
  have ho := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.appendIso_vectorTensorAt K s (n + t) f (Fin.append (g j) h)
    (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K s f : ℤ)) (c + (q + -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K t h : ℤ))) z rfl
    (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree_append]; have := hg j; omega) (by omega)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt_refl] at ho
  rw [ho]


end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

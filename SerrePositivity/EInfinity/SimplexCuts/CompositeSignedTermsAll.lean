module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSignedTerms

/-!
# 元の共通整数次数での符号付き切断項の比較

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §301。
同じ指定面・整数係数・次数移送を保ち、斉次テンソルの比較を元の加群の等式へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- 零となる退化項も保った、元の全切断の符号付き比較（BF §2.2.6）。 -/
lemma positiveComposite_signedCutTerm_eq_nested_all (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (x : S _⦋q⦌) :
    (Surjection.compositionSign u v k c.1 *
      cutSign c.2 (positiveCompositeCutWord u v k c.1).val) •
      cutTensorAt A S c.2 (positiveCompositeCutWord u v k c.1) x =
      positiveNestedCutCoefficient u v k (positiveCompositeNestedMap u v k c) •
        vectorTensorAt (chains A S) (m + (n + 1))
          (fun a =>
            ⟨(positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1,
              gen A S
                (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1
                (S.map (SimplexCategory.mkHom
                  (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).2).op x)⟩)
          (-((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ))
          (by rw [vectorDegree, positiveComposite_nested_degreeSum]) := by
  by_cases h : Nondegenerate c.2 (positiveCompositeCutWord u v k c.1).val
  · exact positiveComposite_signedCutTerm_eq_nested A S u v k c h x
  · have hz : cutTensorAt A S c.2 (positiveCompositeCutWord u v k c.1) x = 0 := by
      unfold cutTensorAt
      rw [cutTensor_eq_zero A S c.2 (positiveCompositeCutWord u v k c.1) h x, map_zero]
    rw [← positiveComposite_cutTensorAt_eq_nested A S u v k c x, hz, smul_zero, smul_zero]

end SerrePositivity.EInfinity.SimplexCuts

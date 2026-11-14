module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeSignedTensors
public import SerrePositivity.EInfinity.SimplexCuts.CutTensorDegreeTransport

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

/-- 同じ二段の指定面族の次数和は、元の合成側の共通次数（BF §2.2.6）。 -/
lemma positiveComposite_nested_degreeSum {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    degreeSum (m + (n + 1))
      (fun a => (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1) =
        m + n + (d + e) + q + 1 - (m + (n + 1)) := by
  have hf := congrArg
    (fun F : Fin (m + (n + 1)) → Σ t : ℕ, Fin (t + 1) →o Fin (q + 1) =>
      degreeSum (m + (n + 1)) (fun a => (F a).1))
    (positiveCompositeFaceFamily_eq_nested u v k c)
  change degreeSum (m + (n + 1)) (outputDegree c.2 (positiveCompositeCutWord u v k c.1)) = _ at hf
  rw [← hf, degreeSum_eq_sum, outputDegree_sum]

/-- 元の切断テンソルは、全ての切断で同じ二段の平坦なテンソルに一致（BF §2.2.6）。 -/
lemma positiveComposite_cutTensorAt_eq_nested (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (x : S _⦋q⦌) :
    cutTensorAt A S c.2 (positiveCompositeCutWord u v k c.1) x =
      vectorTensorAt (chains A S) (m + (n + 1))
          (fun a =>
            ⟨(positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1,
              gen A S
                (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1
                (S.map (SimplexCategory.mkHom
                  (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).2).op x)⟩)
          (-((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ))
          (by rw [vectorDegree, positiveComposite_nested_degreeSum]) := by
  apply eq_of_heq
  have hf := faceFamily_tensor_heq A S (positiveCompositeFaceFamily u v k c)
    (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c))
    (positiveCompositeFaceFamily_eq_nested u v k c) x 1 1 rfl
  simp only [one_smul] at hf
  have hraw : HEq (cutTensor A S c.2 (positiveCompositeCutWord u v k c.1) x)
      (vectorTensor (chains A S) (m + (n + 1)) (fun a =>
        ⟨(positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1,
          gen A S
            (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1
            (S.map (SimplexCategory.mkHom
              (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).2).op
                x)⟩)) := by
    exact hf
  have hcast : HEq (cutTensorAt A S c.2 (positiveCompositeCutWord u v k c.1) x)
      (cutTensor A S c.2 (positiveCompositeCutWord u v k c.1) x) :=
    module_eqToHom_apply_heq _ _ _ _
  apply HEq.trans hcast
  apply HEq.trans hraw
  exact (vectorTensorAt_heq (chains A S) (m + (n + 1)) _ _ _).symm

end SerrePositivity.EInfinity.SimplexCuts

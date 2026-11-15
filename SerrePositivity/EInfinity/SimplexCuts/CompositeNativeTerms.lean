module

public import SerrePositivity.EInfinity.SimplexCuts.VectorTensorTargetTransport
public import SerrePositivity.EInfinity.SimplexCuts.CompositeSignedTermsAll

/-!
# 元の総次数での全合成項と同じ二段項

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §315。
同じ総次数・実際の複体射の値・全有限添字を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元の総次数における全合成項は、同じ二段の実項に一致（BF §2.2.6）。 -/
lemma positiveCompositeCutTerm_eq_nested_tensor (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) (x : S _⦋q⦌) :
    positiveCompositeCutTerm A S u v k c x =
      positiveNestedCutCoefficient u v k (positiveCompositeNestedMap u v k c) •
        vectorTensorAt (chains A S) (m + (n + 1))
          (fun a => ⟨(positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1,
            gen A S (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1
              (S.map (SimplexCategory.mkHom
                (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).2).op x)⟩)
          (-((d + e + q : ℕ) : ℤ))
          (by rw [vectorDegree, positiveComposite_nested_degreeSum]
              have hn : m + n + (d + e) + q + 1 - (m + (n + 1)) = d + e + q := by omega
              rw [hn]) := by
  have ht : -((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ) =
      -((d + e + q : ℕ) : ℤ) := by congr 1; congr 1; omega
  have h := congrArg (fun z =>
    (eqToHom (congrArg (fun t : ℤ => (power (chains A S) (m + (n + 1))).X t) ht)).hom z)
    (positiveComposite_signedCutTerm_eq_nested_all A S u v k c x)
  let f (a : Fin (m + (n + 1))) : Σ d : ℕ, (chains A S).X (-(d : ℤ)) :=
    ⟨(positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1,
      gen A S (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1
        (S.map (SimplexCategory.mkHom
          (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).2).op x)⟩
  have hzero : -(vectorDegree (chains A S) (m + (n + 1)) f : ℤ) =
      -((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ) := by
    change -(degreeSum (m + (n + 1))
      (fun a => (positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) a).1) : ℤ) = _
    rw [positiveComposite_nested_degreeSum]
  have hone : -(vectorDegree (chains A S) (m + (n + 1)) f : ℤ) =
      -((d + e + q : ℕ) : ℤ) := hzero.trans ht
  have htrans := vectorTensorAt_target_transport (chains A S) (m + (n + 1)) f _ _
    hzero hone ht
  rw [map_zsmul, map_zsmul, htrans] at h
  simpa only [positiveCompositeCutTerm, cutTerm, map_zsmul, smul_smul] using h

end SerrePositivity.EInfinity.SimplexCuts

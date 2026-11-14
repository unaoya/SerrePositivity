module

public import SerrePositivity.EInfinity.SimplexCuts.PositiveCompositeBalancePerm

/-!
# 正の合成切断と二段切断の元の符号付き実項

Berger–Fresse §2.2.6、M14 L12a の正の枝、報告 §304。
同じ全有限添字・整数係数・元の生成元の値を保つ。nullaryは別に残す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial

/-- 元の合成側の項と、負号を付けた元の二段側の項（BF §2.2.6）。 -/
def positiveCompositeBalanceTerm (A : Type u) [CommRing A] (S : SSet.{0})
    {m n d e : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (q : ℕ)
    (i : PositiveCompositeCutIndex u v k q ⊕ PositiveNestedCutIndex u v k q) (x : S _⦋q⦌) :
    (power (chains A S) (m + (n + 1))).X
      (-((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ)) :=
  match i with
  | Sum.inl c => (Surjection.compositionSign u v k c.1 *
      cutSign c.2 (positiveCompositeCutWord u v k c.1).val) •
      cutTensorAt A S c.2 (positiveCompositeCutWord u v k c.1) x
  | Sum.inr c => -(positiveNestedCutCoefficient u v k c •
      vectorTensorAt (chains A S) (m + (n + 1))
        (fun a => ⟨(positiveNestedFaceFamily u v k c a).1,
          gen A S (positiveNestedFaceFamily u v k c a).1
            (S.map (SimplexCategory.mkHom (positiveNestedFaceFamily u v k c a).2).op x)⟩)
        (-((m + n + (d + e) + q + 1 - (m + (n + 1)) : ℕ) : ℤ))
        (by rw [vectorDegree, positiveNested_degreeSum]))

end SerrePositivity.EInfinity.SimplexCuts

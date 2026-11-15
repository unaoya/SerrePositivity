module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeNativeTerms
public import SerrePositivity.EInfinity.SimplexCuts.CompositeCochainCutSum

/-!
# 元の係数合成と実際の二段余作用の基底値

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

lemma cochainAction_composition_basis_eq_iterated (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) :
    (cochainAction A S (m + (n + 1))).f (-((d + e + q : ℕ) : ℤ))
      (ιTensorObj (Surjection.complex A (m + (n + 1))) (chains A S)
        (-((d + e : ℕ) : ℤ)) (-(q : ℤ)) (-((d + e + q : ℕ) : ℤ)) (by omega)
        ((Surjection.complexXIso A (m + (n + 1)) (d + e)).inv
          (Surjection.compositionOnWords A u v k) ⊗ₜ[A] gen A S q x)) =
      (iteratedCochainAction A S m (n + 1) k).f (-((d + e + q : ℕ) : ℤ))
        (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A (n + 1)) (chains A S)
          (-(d : ℤ) + -(e : ℤ)) (-(q : ℤ)) (-((d + e + q : ℕ) : ℤ)) (by omega)
          (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A (n + 1))
            (-(d : ℤ)) (-(e : ℤ)) (-(d : ℤ) + -(e : ℤ)) rfl
            ((Surjection.complexXIso A (m + 1) d).inv
              (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A (n + 1) e).inv
                (Surjection.basis A (n + 1) e (ULift.up v))) ⊗ₜ[A] gen A S q x)) := by
  rw [cochainAction_composition_cut_sum, iteratedCochainAction_basis_nested_cut_sum]
  let F (c : PositiveNestedCutIndex u v k q) :
      (power (chains A S) (m + (n + 1))).X (-((d + e + q : ℕ) : ℤ)) :=
    positiveNestedCutCoefficient u v k c •
      vectorTensorAt (chains A S) (m + (n + 1))
        (fun a => ⟨(positiveNestedFaceFamily u v k c a).1,
          gen A S (positiveNestedFaceFamily u v k c a).1
            (S.map (SimplexCategory.mkHom (positiveNestedFaceFamily u v k c a).2).op x)⟩)
        (-((d + e + q : ℕ) : ℤ))
        (by rw [vectorDegree, positiveNested_degreeSum]
            have hn : m + n + (d + e) + q + 1 - (m + (n + 1)) = d + e + q := by omega
            rw [hn])
  have hs := (positiveCompositeNestedEquiv u v k q).sum_comp F
  change (∑ c, positiveCompositeCutTerm A S u v k c x) = ∑ c, F c
  rw [← hs]
  apply Finset.sum_congr rfl
  intro c _
  exact positiveCompositeCutTerm_eq_nested_tensor A S u v k c x

end SerrePositivity.EInfinity.SimplexCuts

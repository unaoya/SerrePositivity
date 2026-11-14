module

public import SerrePositivity.EInfinity.SimplexCuts.IteratedCochainAction
public import SerrePositivity.EInfinity.SimplexCuts.NestedCutCoefficients
public import Mathlib.Tactic.Ring

/-!
# 元の二段余作用の外側切断和と二係数交換

Berger–Fresse §2.2.6・§3.1、M14 L12a の既存構成の法則、報告 §308。
同じ複体射・整数係数・全切断を保って展開する。
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

/-- 元の二段切断の係数は、実際の二つの係数交換の積（BF §3.1）。 -/
lemma positiveNestedCutCoefficient_eq_koszul {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) :
    positiveNestedCutCoefficient u v k c =
      ((-(d : ℤ) * -(e : ℤ)).negOnePow : ℤ) *
        (cutSign c.1 (positiveWord u).val *
          (((-(e : ℤ) * -(positiveNestedPrefixDegree u k c.1 : ℤ)).negOnePow : ℤ) *
            cutSign c.2 (positiveWord v).val)) := by
  simp only [positiveNestedCutCoefficient, neg_mul_neg, ← Nat.cast_mul,
    Int.coe_negOnePow_natCast, pow_add]
  ring

/-- 実際の二段余作用の外側を、元の全切断和へ展開する（BF §2.2.6・§3.1）。 -/
lemma iteratedCochainAction_basis_outer_cut_sum (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) + -(q : ℤ) = z) :
    (iteratedCochainAction A S m (n + 1) k).f z
      (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A (n + 1)) (chains A S)
        (-(d : ℤ) + -(e : ℤ)) (-(q : ℤ)) z hz
        (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A (n + 1))
          (-(d : ℤ)) (-(e : ℤ)) (-(d : ℤ) + -(e : ℤ)) rfl
          ((Surjection.complexXIso A (m + 1) d).inv
            (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (Surjection.complexXIso A (n + 1) e).inv
              (Surjection.basis A (n + 1) e (ULift.up v))) ⊗ₜ[A] gen A S q x)) =
      (-(d : ℤ) * -(e : ℤ)).negOnePow •
        ∑ s : Cut (m + d) q, cutSign s (positiveWord u).val •
          (tensorCoInsertionAction (chains A S) (Surjection.complex A (n + 1)) m (n + 1) k
            (cochainAction A S (n + 1))).f z
            (ιTensorObj (Surjection.complex A (n + 1)) (power (chains A S) (m + 1))
              (-(e : ℤ)) (-(d : ℤ) + -(q : ℤ)) z (by omega)
              ((Surjection.complexXIso A (n + 1) e).inv
                (Surjection.basis A (n + 1) e (ULift.up v)) ⊗ₜ[A]
                vectorTensorAt (chains A S) (m + 1)
                  (fun a => ⟨outputDegree s (positiveWord u) a,
                    gen A S (outputDegree s (positiveWord u) a)
                      (S.map (face s (positiveWord u) a).op x)⟩)
                  (-(d : ℤ) + -(q : ℤ))
                  (by rw [vectorDegree, degreeSum_eq_sum, outputDegree_sum]
                      have hnat : m + d + q + 1 - (m + 1) = d + q := by omega
                      rw [hnat]; omega))) := by
  rw [iteratedCochainAction_apply, cochainAction_basis_cut_sum A S u x _ rfl]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_zsmul]

end SerrePositivity.EInfinity.SimplexCuts

module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryRepeatedCochainAction
public import SerrePositivity.EInfinity.Surjection.CompositionBoundaryCases

/-!
# 指定色の反復出現における元の空語合成則

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §346。
元の係数合成の零性と、同じ四射の二段作用の零性を連結する。
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

/-- 反復出現の空語合成則は元の二つの複体射の値で一致（BF §2.2.6）。 -/
lemma cochainAction_composition_nullary_repeated_eq_iterated (S : SSet.{0}) {m d q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord 0 0)
    (k : Fin (m + 1)) (hcount : Surjection.occurrenceCount u.val k ≠ 1) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(0 : ℤ) + -(q : ℤ) = z) :
    (cochainAction A S (m + 0)).f z
      (ιTensorObj (Surjection.complex A (m + 0)) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) z (by omega)
        ((Surjection.complexXIso A (m + 0) d).inv
          (Surjection.compositionOnWords A u v k) ⊗ₜ[A] gen A S q x)) =
    (iteratedCochainAction A S m 0 k).f z
      (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A 0) (chains A S)
        (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) z hz
        (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A 0)
          (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
          ((Surjection.complexXIso A (m + 1) d).inv
            (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (Surjection.complexXIso A 0 0).inv
              (Surjection.basis A 0 0 (ULift.up v))) ⊗ₜ[A] gen A S q x)) := by
  calc
    _ = 0 := by
      rw [Surjection.compositionOnWords_nullary_of_count_ne_one A u v k hcount]
      simp only [map_zero, TensorProduct.zero_tmul]
    _ = _ := (iteratedCochainAction_nullary_repeated_basis_eq_zero A S u v k hcount x z hz).symm

end SerrePositivity.EInfinity.SimplexCuts

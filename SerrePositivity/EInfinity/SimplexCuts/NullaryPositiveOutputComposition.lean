module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryNondegenerateComposition
public import SerrePositivity.EInfinity.SimplexCuts.NullaryDegenerateComposition
public import SerrePositivity.EInfinity.SimplexCuts.NullaryRepeatedComposition

/-!
# 正の出力arityの空語合成の全基底上の一致

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §363。
同じ係数合成と実際の二段作用について、反復出現と退化・非退化の全分岐を合わせる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 正の出力arityの実際の空語合成則は全ての係数基底で一致（BF §2.2.6）。 -/
lemma cochainAction_composition_nullary_positive_output_eq_iterated
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d q : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (x : S _⦋q⦌) :
    (cochainAction A S ((m + 1) + 0)).f (-(d : ℤ) + -(q : ℤ))
      (ιTensorObj (Surjection.complex A ((m + 1) + 0)) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) rfl
        ((Surjection.complexXIso A ((m + 1) + 0) d).inv
          (Surjection.compositionOnWords A u ν k) ⊗ₜ[A] gen A S q x)) =
      (iteratedCochainAction A S (m + 1) 0 k).f (-(d : ℤ) + -(q : ℤ))
        (ιTensorObj (Surjection.complex A (m + 2) ⊗ Surjection.complex A 0) (chains A S)
          (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) (by omega)
          (ιTensorObj (Surjection.complex A (m + 2)) (Surjection.complex A 0)
            (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
            ((Surjection.complexXIso A (m + 2) d).inv
              (Surjection.basis A (m + 2) d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A 0 0).inv
                (Surjection.basis A 0 0 (ULift.up ν))) ⊗ₜ[A] gen A S q x)) := by
  by_cases hc : Surjection.occurrenceCount u.val k = 1
  · let ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 :=
      Eq.mp (congrArg (fun n => Surjection.OverlapPartition n 0) hc.symm)
        (Surjection.OverlapPartition.single 0)
    by_cases hnd : Surjection.Nondegenerate (IntervalCuts.nullaryRawWord u ν k ρ)
    · let w : Surjection.BasisWord (m + 1) d :=
        ⟨IntervalCuts.nullaryRawWord u ν k ρ, IntervalCuts.nullaryRawWord_surjective u ν k ρ, hnd⟩
      exact cochainAction_composition_nullary_nondegenerate_eq_iterated A S u ν k ρ w rfl x
    · exact cochainAction_composition_nullary_degenerate_eq_iterated A S u ν k ρ hnd x
  · exact cochainAction_composition_nullary_repeated_eq_iterated A S u ν k hc x
      (-(d : ℤ) + -(q : ℤ)) (by omega)

end SerrePositivity.EInfinity.SimplexCuts

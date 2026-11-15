module

public import SerrePositivity.EInfinity.SimplexCuts.IteratedOuterCutSumAll
public import SerrePositivity.EInfinity.SimplexCuts.CochainNullaryInsertionDegrees
public import SerrePositivity.EInfinity.SimplexCuts.NullaryZeroColor
public import SerrePositivity.EInfinity.SimplexCuts.PositiveNestedCuts

/-!
# 指定色の反復出現における元の空語二段余作用の零性

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §345。
元の全外側切断の指定色の出力次数が正であることから、実際の空語作用で消す。
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

/-- 反復出現する指定色への実際の空語二段作用は零（BF §2.2.6）。 -/
lemma iteratedCochainAction_nullary_repeated_basis_eq_zero (S : SSet.{0}) {m d q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord 0 0)
    (k : Fin (m + 1)) (hcount : Surjection.occurrenceCount u.val k ≠ 1) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(0 : ℤ) + -(q : ℤ) = z) :
    (iteratedCochainAction A S m 0 k).f z
      (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A 0) (chains A S)
        (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) z hz
        (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A 0)
          (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
          ((Surjection.complexXIso A (m + 1) d).inv
            (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
            (Surjection.complexXIso A 0 0).inv
              (Surjection.basis A 0 0 (ULift.up v))) ⊗ₜ[A] gen A S q x)) = 0 := by
  erw [iteratedCochainAction_basis_outer_cut_sum_all A S u v k x z hz]
  simp only [Nat.cast_zero, neg_zero, mul_zero, Int.negOnePow_zero, one_smul]
  apply Finset.sum_eq_zero
  intro s _
  have hpos : 0 < outputDegree s (positiveWord u) k := by
    by_contra h
    have hzero : outputDegree s (positiveWord u) k = 0 := by omega
    have hc := outputDegree_zero_occurrenceCount s (positiveWord u) k hzero
    rw [positiveWord_occurrenceCount] at hc
    exact hcount hc
  let f (a : Fin (m + 1)) : Σ d : ℕ, (chains A S).X (-(d : ℤ)) :=
    ⟨outputDegree s (positiveWord u) a, gen A S (outputDegree s (positiveWord u) a)
      (S.map (face s (positiveWord u) a).op x)⟩
  have hp : -(vectorDegree (chains A S) (m + 1) f : ℤ) = -(d : ℤ) + -(q : ℤ) := by
    rw [vectorDegree, degreeSum_eq_sum]
    change -((∑ a, outputDegree s (positiveWord u) a : ℕ) : ℤ) = _
    rw [outputDegree_sum]
    have hnat : m + d + q + 1 - (m + 1) = d + q := by omega
    rw [hnat]
    omega
  have H := tensorCoInsertionAction_cochain_nullary_positive_at A S v k f hpos
    (-(d : ℤ) + -(q : ℤ)) z hp (by omega)
  exact (congrArg (fun y => cutSign s (positiveWord u).val • y) H).trans (smul_zero _)

end SerrePositivity.EInfinity.SimplexCuts

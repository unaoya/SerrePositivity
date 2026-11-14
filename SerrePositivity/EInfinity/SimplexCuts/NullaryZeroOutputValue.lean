module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryCoefficientWords
public import SerrePositivity.EInfinity.SimplexCuts.CochainNullaryInsertionDegrees
public import SerrePositivity.EInfinity.SimplexCuts.IteratedOuterCutSumAll
public import SerrePositivity.EInfinity.SimplexCuts.ZeroFaceGenerator
public import SerrePositivity.EInfinity.SimplexCuts.CutGeneratorFamilies
public import SerrePositivity.EInfinity.SimplexCuts.NullaryPointCaesuras

/-!
# 零出力arityの元の空語合成の零単体の値

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §365。
元の唯一のCutを使い、同じ空語係数と実際の余単位を評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 零出力arityの同じ空語合成の零単体の値は一致（BF §2.2.6）。 -/
lemma cochainAction_composition_nullary_output_zero_degree_zero
    (A : Type u) [CommRing A] (S : SSet.{0}) (u : Surjection.BasisWord 1 0)
    (ν : Surjection.BasisWord 0 0) (x : S _⦋0⦌) :
    (cochainAction A S 0).f 0
      (ιTensorObj (Surjection.complex A 0) (chains A S) 0 0 0 rfl
        ((Surjection.complexXIso A 0 0).inv
          (Surjection.compositionOnWords A u ν 0) ⊗ₜ[A] gen A S 0 x)) =
      (iteratedCochainAction A S 0 0 0).f 0
        (ιTensorObj (Surjection.complex A 1 ⊗ Surjection.complex A 0) (chains A S) 0 0 0 rfl
          (ιTensorObj (Surjection.complex A 1) (Surjection.complex A 0) 0 0 0 rfl
            ((Surjection.complexXIso A 1 0).inv
              (Surjection.basis A 1 0 (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A 0 0).inv
                (Surjection.basis A 0 0 (ULift.up ν))) ⊗ₜ[A] gen A S 0 x)) := by
  let e := singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))
  have hc : Surjection.occurrenceCount u.val (0 : Fin 1) = 1 := by
    have hu : u.val 0 = 0 := Subsingleton.elim _ _
    simp [Surjection.occurrenceCount, List.ofFn_succ, hu]
  let ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val 0) 0 :=
    Eq.mp (congrArg (fun n => Surjection.OverlapPartition n 0) hc.symm)
      (Surjection.OverlapPartition.single 0)
  have hcoeff : Surjection.compositionOnWords A u ν 0 = Surjection.basis A 0 0 (ULift.up ν) :=
    compositionOnWords_nullary_eq_basis_of_raw A u ν 0 ρ ν (by funext i; exact Fin.elim0 i)
  let s : Cut 0 0 := ⟨∅, rfl⟩
  have hcutunique (t : Cut 0 0) : t = s := Subtype.ext (Finset.card_eq_zero.mp t.property)
  let f := cutGeneratorFamily A S s (positiveWord u) x
  have hout : outputDegree s (positiveWord u) (0 : Fin 1) = 0 := by
    have H := outputDegree_sum s (positiveWord u)
    change (∑ a : Fin 1, outputDegree s (positiveWord u) a) = 0 at H
    rw [Fin.sum_univ_one] at H
    exact H
  obtain ⟨y, hy⟩ := faceData_generator_zero A S
    (⟨outputDegree s (positiveWord u) 0, vertices s (positiveWord u) 0⟩ :
      Σ d : ℕ, Fin (d + 1) →o Fin 1) hout x
  have hdegree : -(vectorDegree (chains A S) 1 f : ℤ) = 0 := by
    rw [vectorDegree_cutGeneratorFamily]
    rfl
  have hθ := tensorCoInsertionAction_cochain_nullary_zero_at A S ν (0 : Fin 1) f y hy
    0 0 hdegree rfl
  have hcae : ¬Surjection.Caesura (positiveWord u).val (0 : Fin 1) :=
    not_caesura_of_unique _ _ (fun (j : Fin 1) _ => by
      apply Fin.ext
      have hj := j.isLt
      omega)
  have hsign : cutSign s (positiveWord u).val = 1 := by
    change (-1 : ℤ) ^
      ((∑ i : Fin 1, ∑ j : Fin 1, if i < j ∧ (positiveWord u).val j < (positiveWord u).val i
        then intervalLength s (positiveWord u).val i * intervalLength s (positiveWord u).val j
        else 0) + ∑ i : Fin 1, if Surjection.Caesura (positiveWord u).val i then hi s i else 0) = 1
    simp only [Fin.sum_univ_one, lt_self_iff_false, false_and, ite_false, hcae,
      zero_add, pow_zero]
  have hL : (cochainAction A S 0).f 0
      (ιTensorObj (Surjection.complex A 0) (chains A S) 0 0 0 rfl
        ((Surjection.complexXIso A 0 0).inv
          (Surjection.compositionOnWords A u ν 0) ⊗ₜ[A] gen A S 0 x)) = e.inv (1 : A) := by
    rw [hcoeff]
    exact cochainAction_nullary_basis_generator_zero A S ν x
  have hR : (iteratedCochainAction A S 0 0 0).f 0
        (ιTensorObj (Surjection.complex A 1 ⊗ Surjection.complex A 0) (chains A S) 0 0 0 rfl
          (ιTensorObj (Surjection.complex A 1) (Surjection.complex A 0) 0 0 0 rfl
            ((Surjection.complexXIso A 1 0).inv
              (Surjection.basis A 1 0 (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A 0 0).inv
                (Surjection.basis A 0 0 (ULift.up ν))) ⊗ₜ[A] gen A S 0 x)) = e.inv (1 : A) := by
    erw [iteratedCochainAction_basis_outer_cut_sum_all A S u ν 0 x 0 rfl]
    simp only [Nat.cast_zero, neg_zero, zero_mul, Int.negOnePow_zero, one_smul]
    rw [Finset.sum_eq_single s]
    · rw [hsign, one_smul]
      exact hθ
    · intro t _ hts
      exact False.elim (hts (hcutunique t))
    · intro hs
      exact False.elim (hs (Finset.mem_univ s))
  exact hL.trans hR.symm

end SerrePositivity.EInfinity.SimplexCuts

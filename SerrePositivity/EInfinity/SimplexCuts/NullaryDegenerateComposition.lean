module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryDegenerateCutSums
public import SerrePositivity.EInfinity.SimplexCuts.NullaryRawLengthValues
public import SerrePositivity.EInfinity.SimplexCuts.NullaryCoefficientWords
public import SerrePositivity.EInfinity.SimplexCuts.NullaryCutIndexTransport
public import SerrePositivity.EInfinity.SimplexCuts.IteratedOuterCutSumAll

/-!
# 退化な実際の空語合成の元の二つの射の値の一致

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §362。
元のraw合成語の退化零項を使い、同じ語長の移送と全Cut和の対応を接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 同じ退化raw空語合成の実際の二つの射の値は一致する（BF §2.2.6）。 -/
lemma cochainAction_composition_nullary_degenerate_eq_iterated
    (A : Type u) [CommRing A] (S : SSet.{0}) {m d q : ℕ}
    (u : Surjection.BasisWord (m + 2) d) (ν : Surjection.BasisWord 0 0) (k : Fin (m + 2))
    (ρ : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0)
    (hdeg : ¬Surjection.Nondegenerate (IntervalCuts.nullaryRawWord u ν k ρ))
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
  let z : ℤ := -(d : ℤ) + -(q : ℤ)
  have hC : (m + 1) + d = (m + d) + 1 := by omega
  have hU : (m + 2) + d = ((m + 1) + d) + 1 := by omega
  have hV : (m + 2) + d = (m + d) + 2 := by omega
  let V : Surjection.Word (m + 2) ((m + d) + 2) :=
    Eq.mp (congrArg (fun L => Surjection.Word (m + 2) L) hV) u
  obtain ⟨p, hp, hu⟩ := unique_position_of_occurrenceCount_one u.val k ρ.count_eq_one_of_empty
  let P : Fin ((m + d) + 2) := Fin.cast hV p
  have hvp : V.val P = k ∧ ∀ j, V.val j = k → j = P := word_eq_mp_unique hV u p k hp hu
  let W : Fin ((m + d) + 1) → Fin (m + 1) :=
    fun i => IntervalCuts.nullaryRawWord u ν k ρ (Fin.cast hC.symm i)
  have hw : ¬Surjection.Nondegenerate W := by
    intro h
    exact hdeg ((raw_nondegenerate_cast_iff hC (IntervalCuts.nullaryRawWord u ν k ρ)).mp h)
  have hvw : ∀ i, k.succAbove (W i) = V.val (P.succAbove i) := by
    intro i
    exact nullaryRawWord_cast_erase_value hC u ν k ρ p hu i
  have hz : -(((m + d) + q + 1 - (m + 1) : ℕ) : ℤ) = z := by dsimp only [z]; omega
  have ho : -(((m + 1) + d + q + 1 - (m + 2) : ℕ) : ℤ) = z := by dsimp only [z]; omega
  let T : (power (chains A S) (m + 2)).X z → (power (chains A S) ((m + 1) + 0)).X z :=
    fun y => (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) (m + 1) 0 k
      (cochainAction A S 0)).f z
      (ιTensorObj (Surjection.complex A 0) (power (chains A S) (m + 2)) 0 z z (zero_add z)
        ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up ν)) ⊗ₜ[A] y))
  have H := sum_nullary_cochain_cut_terms_of_raw_degenerate A S V W P k
    hvp.1 hvw hw ν x z hz
  have HT := sum_cutGenerator_terms_eq_mp A S hC (positiveWord u) x z ho T
  have hword : Eq.mp (congrArg (fun L => Surjection.Word (m + 2) (L + 1)) hC)
      (positiveWord u) = V := by
    change Eq.mp (congrArg (fun L => Surjection.Word (m + 2) L)
      (congrArg (fun L : ℕ => L + 1) hC))
      (Eq.mp (congrArg (fun L => Surjection.Word (m + 2) L) hU) u) = V
    exact word_eq_mp_trans hU (congrArg (fun L : ℕ => L + 1) hC) u
  let F (a : Surjection.Word (m + 2) ((m + d) + 2)) :
      (power (chains A S) ((m + 1) + 0)).X z :=
    ∑ s : Cut ((m + d) + 1) q, cutSign s a.val •
      T (vectorTensorAt (chains A S) (m + 2) (cutGeneratorFamily A S s a x) z
        (by rw [vectorDegree_cutGeneratorFamily]; dsimp only [z]; omega))
  change (∑ s : Cut ((m + 1) + d) q, cutSign s (positiveWord u).val •
    T (vectorTensorAt (chains A S) (m + 2) (cutGeneratorFamily A S s (positiveWord u) x) z
      (by rw [vectorDegree_cutGeneratorFamily]; exact ho))) =
    F (Eq.mp (congrArg (fun L => Surjection.Word (m + 2) (L + 1)) hC)
      (positiveWord u)) at HT
  have HT' := HT.trans (congrArg F hword)
  have hL : (cochainAction A S ((m + 1) + 0)).f (-(d : ℤ) + -(q : ℤ))
      (ιTensorObj (Surjection.complex A ((m + 1) + 0)) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) rfl
        ((Surjection.complexXIso A ((m + 1) + 0) d).inv
          (Surjection.compositionOnWords A u ν k) ⊗ₜ[A] gen A S q x)) = 0 := by
    rw [compositionOnWords_nullary_eq_zero_of_raw_degenerate A u ν k ρ hdeg]
    simp only [map_zero, TensorProduct.zero_tmul]
  have hR : (iteratedCochainAction A S (m + 1) 0 k).f (-(d : ℤ) + -(q : ℤ))
        (ιTensorObj (Surjection.complex A (m + 2) ⊗ Surjection.complex A 0) (chains A S)
          (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) (by omega)
          (ιTensorObj (Surjection.complex A (m + 2)) (Surjection.complex A 0)
            (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
            ((Surjection.complexXIso A (m + 2) d).inv
              (Surjection.basis A (m + 2) d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A 0 0).inv
                (Surjection.basis A 0 0 (ULift.up ν))) ⊗ₜ[A] gen A S q x)) = 0 := by
    erw [iteratedCochainAction_basis_outer_cut_sum_all A S u ν k x
      (-(d : ℤ) + -(q : ℤ)) (by omega)]
    simp only [Nat.cast_zero, neg_zero, mul_zero, Int.negOnePow_zero, one_smul]
    change (∑ s : Cut ((m + 1) + d) q, cutSign s (positiveWord u).val •
      T (vectorTensorAt (chains A S) (m + 2) (cutGeneratorFamily A S s (positiveWord u) x) z
        (by rw [vectorDegree_cutGeneratorFamily]; exact ho))) = 0
    exact HT'.trans H
  exact hL.trans hR.symm

end SerrePositivity.EInfinity.SimplexCuts

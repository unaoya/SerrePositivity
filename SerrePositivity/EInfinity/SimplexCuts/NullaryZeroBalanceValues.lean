module

public import SerrePositivity.EInfinity.SimplexCuts.CochainCompositionBasisAll
public import SerrePositivity.EInfinity.SimplexCuts.NullaryNativeBalancePairing

/-!
# 零出力の元の空語合成の有限項

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §377。
全分割・余単位の一項と元の全Cutを残し、同じ唯一Cutの値を比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 空作用の余単位の項と元の全大Cutの直和（BF §2.2.6）。 -/
abbrev NullaryZeroBalanceIndex (u : Surjection.BasisWord 1 0) (k : Fin 1) (q : ℕ) :=
  (Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × PUnit.{1}) ⊕ Cut 0 q

/-- 元の合成符号を持つ空作用の余単位の一項（BF §2.2.6）。 -/
def nullaryZeroCompositeTerm (A : Type u) [CommRing A] (S : SSet.{0})
    (u : Surjection.BasisWord 1 0) (ν : Surjection.BasisWord 0 0) (k : Fin 1) {q : ℕ}
    (c : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × PUnit.{1})
    (x : S _⦋q⦌) : (power (chains A S) 0).X (-(q : ℤ)) :=
  Surjection.compositionSign u ν k c.1 •
    (cochainAction A S 0).f (-(q : ℤ))
      (ιTensorObj (Surjection.complex A 0) (chains A S) 0 (-(q : ℤ)) (-(q : ℤ)) (by omega)
        ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up ν)) ⊗ₜ[A]
          gen A S q x))

/-- 零出力でも元の全大Cutの実際の二段項を保持する（BF §2.2.6）。 -/
def nullaryZeroOuterTerm (A : Type u) [CommRing A] (S : SSet.{0})
    (u : Surjection.BasisWord 1 0) (ν : Surjection.BasisWord 0 0) (k : Fin 1) {q : ℕ}
    (s : Cut 0 q) (x : S _⦋q⦌) : (power (chains A S) 0).X (-(q : ℤ)) :=
  cutSign s (positiveWord u).val •
    (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) 0 0 k
      (cochainAction A S 0)).f (-(q : ℤ))
      (ιTensorObj (Surjection.complex A 0) (power (chains A S) (0 + 1))
        (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + -(q : ℤ)) (-(q : ℤ))
        (by omega) ((Surjection.complexXIso A 0 0).inv
          (Surjection.basis A 0 0 (ULift.up ν)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (0 + 1)
            (fun a => ⟨outputDegree s (positiveWord u) a,
              gen A S (outputDegree s (positiveWord u) a)
                (S.map (face s (positiveWord u) a).op x)⟩)
            (-((0 : ℕ) : ℤ) + -(q : ℤ))
            (by rw [vectorDegree, degreeSum_eq_sum, outputDegree_sum]; simp)))

/-- 元の全Cut展開を同じ唯一Cutで評価した一項ごとの一致（BF §2.2.6）。 -/
lemma nullaryZeroCompositeTerm_eq_outer (A : Type u) [CommRing A] (S : SSet.{0})
    (u : Surjection.BasisWord 1 0) (ν : Surjection.BasisWord 0 0) (k : Fin 1) {q : ℕ}
    (c : Surjection.OverlapPartition (Surjection.occurrenceCount u.val k) 0 × PUnit.{1})
    (s : Cut 0 q) (x : S _⦋q⦌) :
    nullaryZeroCompositeTerm A S u ν k c x = nullaryZeroOuterTerm A S u ν k s x := by
  have H := cochainAction_composition_basis_eq_iterated_all A S u ν k x (-(q : ℤ)) (by omega)
  rw [compositionOnWords_nullary_eq_basis_of_raw A u ν k c.1 ν
    (by funext i; exact Fin.elim0 i)] at H
  erw [iteratedCochainAction_basis_outer_cut_sum_all A S u ν k x _ (by omega)] at H
  simp only [Nat.cast_zero, neg_zero, zero_mul, Int.negOnePow_zero, one_smul] at H
  have hcutunique (t : Cut 0 q) : t = s :=
    Subtype.ext ((Finset.card_eq_zero.mp t.property).trans (Finset.card_eq_zero.mp s.property).symm)
  rw [Finset.sum_eq_single s] at H
  · unfold nullaryZeroCompositeTerm nullaryZeroOuterTerm
    rw [Surjection.compositionSign_inner_degree_zero, one_smul]
    convert H using 1
    simp
  · intro t _ hts
    exact False.elim (hts (hcutunique t))
  · intro hs
    exact False.elim (hs (Finset.mem_univ s))

end SerrePositivity.EInfinity.SimplexCuts

module

public import SerrePositivity.EInfinity.SimplexCuts.CochainNullaryValues
public import SerrePositivity.EInfinity.SimplexCuts.VectorCoInsertionActionEvaluation
public import SerrePositivity.EInfinity.SimplexCuts.VectorCoInsertionActionSums

/-!
# 元の出力族への実際の空語余演算の代入

Berger–Fresse §2.2.6・§3.1、M14 L12a、報告 §341。
元の零arityの作用の実際の値を使い、選んだ因子の消去と正次数の零性を読む。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open IntervalCuts (prefixFamily suffixFamily insertionFamily)
open scoped Simplicial

/-- 選んだ正次数の因子への実際の空語作用は零（BF §2.2.6）。 -/
lemma tensorCoInsertionAction_cochain_nullary_positive (A : Type u) [CommRing A]
    (S : SSet.{0}) {m : ℕ} (v : Surjection.BasisWord 0 0) (i : Fin (m + 1))
    (f : Fin (m + 1) → Σ d : ℕ, (chains A S).X (-(d : ℤ)))
    (hpos : 0 < (f i).1) (z : ℤ)
    (hz : 0 + (-(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
      (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ))) = z) :
    (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) m 0 i
      (cochainAction A S 0)).f z
      (ιTensorObj (Surjection.complex A 0) (power (chains A S) (m + 1)) 0
        (-(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
          (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ))) z hz
        ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (m + 1) f _
            (by have h := vectorDegree_family_blocks (chains A S) f i; omega))) = 0 := by
  have H := tensorCoInsertionAction_vector_sum_apply (ι := Fin 0)
    (chains A S) (Surjection.complex A 0) m 0 i (cochainAction A S 0) 0 z f
    (fun j => Fin.elim0 j) hz
    ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up v)))
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) (by
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      let _ : Subsingleton ((power (chains A S) 0).X (0 + -((f i).1 : ℤ))) := by
        change Subsingleton (((single (ModuleCat A) (.up ℤ) 0).obj
          (𝟙_ (ModuleCat A))).X (0 + -((f i).1 : ℤ)))
        exact ModuleCat.isZero_iff_subsingleton.mp
          (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) _ (by omega))
      exact Subsingleton.elim _ _)
  simpa only [Finset.univ_eq_empty, Finset.sum_empty, smul_zero] using H

/-- 選んだ同じ零単体への空語作用は、元の因子だけを消す（BF §2.2.6）。 -/
lemma tensorCoInsertionAction_cochain_nullary_zero (A : Type u) [CommRing A]
    (S : SSet.{0}) {m : ℕ} (v : Surjection.BasisWord 0 0) (i : Fin (m + 1))
    (f : Fin (m + 1) → Σ d : ℕ, (chains A S).X (-(d : ℤ)))
    (x : S _⦋0⦌) (hx : f i = ⟨0, gen A S 0 x⟩) (z : ℤ)
    (hz : 0 + (-(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
      (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ))) = z) :
    (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) m 0 i
      (cochainAction A S 0)).f z
      (ιTensorObj (Surjection.complex A 0) (power (chains A S) (m + 1)) 0
        (-(vectorDegree (chains A S) i.val (prefixFamily f i) : ℤ) +
          (-((f i).1 : ℤ) + -(vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℤ))) z hz
        ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A]
          vectorTensorAt (chains A S) (m + 1) f _
            (by have h := vectorDegree_family_blocks (chains A S) f i; omega))) =
      vectorTensorAt (chains A S) (m + 0)
        (insertionFamily f (fun j : Fin 0 => Fin.elim0 j) i) z
        (by rw [vectorDegree_insertionFamily]
            have hi : (f i).1 = 0 := congrArg Sigma.fst hx
            change -(vectorDegree (chains A S) i.val (prefixFamily f i) + 0 +
              vectorDegree (chains A S) (m - i.val) (suffixFamily f i) : ℕ) = z
            omega) := by
  let g : Fin 0 → Σ d : ℕ, (chains A S).X (-(d : ℤ)) := fun j => Fin.elim0 j
  have hi : (f i).1 = 0 := congrArg Sigma.fst hx
  have hg : -(vectorDegree (chains A S) 0 g : ℤ) = 0 + -((f i).1 : ℤ) := by
    change (0 : ℤ) = 0 + -((f i).1 : ℤ)
    rw [hi]
    rfl
  have hvalue (y : Σ d : ℕ, (chains A S).X (-(d : ℤ)))
      (hy : y = ⟨0, gen A S 0 x⟩)
      (hg : -(vectorDegree (chains A S) 0 g : ℤ) = 0 + -(y.1 : ℤ)) :
      (cochainAction A S 0).f (0 + -(y.1 : ℤ))
        (ιTensorObj (Surjection.complex A 0) (chains A S) 0 (-(y.1 : ℤ))
          (0 + -(y.1 : ℤ)) rfl
          ((Surjection.complexXIso A 0 0).inv
            (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A] y.2)) =
        (1 : ℤ) • vectorTensorAt (chains A S) 0 g (0 + -(y.1 : ℤ)) hg := by
    subst y
    change (cochainAction A S 0).f 0
      (ιTensorObj (Surjection.complex A 0) (chains A S) 0 0 0 rfl
        ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A]
          gen A S 0 x)) =
      (1 : ℤ) • (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)
    rw [one_smul]
    exact cochainAction_nullary_basis_generator_zero A S v x
  have H := tensorCoInsertionAction_vector_apply
    (chains A S) (Surjection.complex A 0) m 0 i (cochainAction A S 0) 0 z f g hz
    ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up v)))
    hg 1 (hvalue (f i) hx hg)
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at H
  exact H

end SerrePositivity.EInfinity.SimplexCuts

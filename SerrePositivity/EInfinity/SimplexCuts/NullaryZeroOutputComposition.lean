module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryZeroOutputValue

/-!
# 零出力arityの空語合成の全次数の一致

Berger–Fresse §1.2.4・§2.2.6、M14 L12a、報告 §366。
元の零単体の値とsingle複体の零対象性を使い、全入力次数を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 零出力arityの実際の空語合成則は全次数で一致（BF §2.2.6）。 -/
lemma cochainAction_composition_nullary_zero_output_eq_iterated
    (A : Type u) [CommRing A] (S : SSet.{0}) {d q : ℕ}
    (u : Surjection.BasisWord 1 d) (ν : Surjection.BasisWord 0 0) (k : Fin 1)
    (x : S _⦋q⦌) :
    (cochainAction A S 0).f (-(d : ℤ) + -(q : ℤ))
      (ιTensorObj (Surjection.complex A 0) (chains A S)
        (-(d : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) rfl
        ((Surjection.complexXIso A 0 d).inv
          (Surjection.compositionOnWords A u ν k) ⊗ₜ[A] gen A S q x)) =
      (iteratedCochainAction A S 0 0 k).f (-(d : ℤ) + -(q : ℤ))
        (ιTensorObj (Surjection.complex A 1 ⊗ Surjection.complex A 0) (chains A S)
          (-(d : ℤ) + -(0 : ℤ)) (-(q : ℤ)) (-(d : ℤ) + -(q : ℤ)) (by omega)
          (ιTensorObj (Surjection.complex A 1) (Surjection.complex A 0)
            (-(d : ℤ)) (-(0 : ℤ)) (-(d : ℤ) + -(0 : ℤ)) rfl
            ((Surjection.complexXIso A 1 d).inv
              (Surjection.basis A 1 d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A 0 0).inv
                (Surjection.basis A 0 0 (ULift.up ν))) ⊗ₜ[A] gen A S q x)) := by
  cases d with
  | succ d => exact isEmptyElim u
  | zero =>
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    cases q with
    | zero => exact cochainAction_composition_nullary_output_zero_degree_zero A S u ν x
    | succ q =>
      let _ : Subsingleton ((power (chains A S) 0).X (-(0 : ℤ) + -((q + 1 : ℕ) : ℤ))) := by
        change Subsingleton (((single (ModuleCat A) (.up ℤ) 0).obj
          (𝟙_ (ModuleCat A))).X (-(0 : ℤ) + -((q + 1 : ℕ) : ℤ)))
        exact ModuleCat.isZero_iff_subsingleton.mp
          (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) _ (by omega))
      exact Subsingleton.elim _ _

end SerrePositivity.EInfinity.SimplexCuts

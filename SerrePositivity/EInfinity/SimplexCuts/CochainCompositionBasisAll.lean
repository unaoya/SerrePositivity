module

public import SerrePositivity.EInfinity.SimplexCuts.CochainCompositionBasis
public import SerrePositivity.EInfinity.SimplexCuts.NullaryPositiveOutputComposition
public import SerrePositivity.EInfinity.SimplexCuts.NullaryZeroOutputComposition

/-!
# 全arity・全係数次数の実際のBF合成則の基底値

Berger–Fresse §2.2.6、M14 L12a、報告 §367。
元の正arity・空語の退化・非退化・零出力の全分岐を同じ射の等式へ合わせる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 全arity・全係数次数で元の二つの射の基底値が厳密に一致（BF §2.2.6）。 -/
lemma cochainAction_composition_basis_eq_iterated_all
    (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord n e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) + -(q : ℤ) = z) :
    (cochainAction A S (m + n)).f z
      (ιTensorObj (Surjection.complex A (m + n)) (chains A S)
        (-((d + e : ℕ) : ℤ)) (-(q : ℤ)) z (by omega)
        ((Surjection.complexXIso A (m + n) (d + e)).inv
          (Surjection.compositionOnWords A u v k) ⊗ₜ[A] gen A S q x)) =
      (iteratedCochainAction A S m n k).f z
        (ιTensorObj (Surjection.complex A (m + 1) ⊗ Surjection.complex A n) (chains A S)
          (-(d : ℤ) + -(e : ℤ)) (-(q : ℤ)) z (by omega)
          (ιTensorObj (Surjection.complex A (m + 1)) (Surjection.complex A n)
            (-(d : ℤ)) (-(e : ℤ)) (-(d : ℤ) + -(e : ℤ)) rfl
            ((Surjection.complexXIso A (m + 1) d).inv
              (Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
              (Surjection.complexXIso A n e).inv
                (Surjection.basis A n e (ULift.up v))) ⊗ₜ[A] gen A S q x)) := by
  cases n with
  | succ n =>
    have he : z = -((d + e + q : ℕ) : ℤ) := by omega
    subst he
    exact cochainAction_composition_basis_eq_iterated A S u v k x
  | zero =>
    cases e with
    | succ e => exact isEmptyElim v
    | zero =>
      have he : z = -(d : ℤ) + -(q : ℤ) := by omega
      subst he
      cases m with
      | zero => exact cochainAction_composition_nullary_zero_output_eq_iterated A S u v k x
      | succ m => exact cochainAction_composition_nullary_positive_output_eq_iterated A S u v k x

end SerrePositivity.EInfinity.SimplexCuts

module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CochainCompositionBasis
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryPositiveOutputComposition
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryZeroOutputComposition

/-!
模型。文献の定義との比較は後で
# 全arity・全係数次数の実際のBF合成則の基底値

Berger–Fresse §2.2.6、M14 L12a、報告 §367。
元の正arity・空語の退化・非退化・零出力の全分岐を同じ射の等式へ合わせる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 全arity・全係数次数で元の二つの射の基底値が厳密に一致（BF §2.2.6）。 -/
lemma cochainAction_composition_basis_eq_iterated_all
    (A : Type u) [CommRing A] (S : SSet.{0}) {m n d e q : ℕ}
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (k : Fin (m + 1)) (x : S _⦋q⦌) (z : ℤ)
    (hz : -(d : ℤ) + -(e : ℤ) + -(q : ℤ) = z) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S (m + n)).f z
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + n)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S)
        (-((d + e : ℕ) : ℤ)) (-(q : ℤ)) z (by omega)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (m + n) (d + e)).inv
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A u v k) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x)) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.iteratedCochainAction A S m n k).f z
        (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1) ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S)
          (-(d : ℤ) + -(e : ℤ)) (-(q : ℤ)) z (by omega)
          (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A (m + 1)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n)
            (-(d : ℤ)) (-(e : ℤ)) (-(d : ℤ) + -(e : ℤ)) rfl
            ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A (m + 1) d).inv
              (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (m + 1) d (ULift.up u)) ⊗ₜ[A]
              (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n e).inv
                (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n e (ULift.up v))) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q x)) := by
  cases n with
  | succ n =>
    have he : z = -((d + e + q : ℕ) : ℤ) := by omega
    subst he
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_composition_basis_eq_iterated A S u v k x
  | zero =>
    cases e with
    | succ e => exact isEmptyElim v
    | zero =>
      have he : z = -(d : ℤ) + -(q : ℤ) := by omega
      subst he
      cases m with
      | zero => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_composition_nullary_zero_output_eq_iterated A S u v k x
      | succ m => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_composition_nullary_positive_output_eq_iterated A S u v k x

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

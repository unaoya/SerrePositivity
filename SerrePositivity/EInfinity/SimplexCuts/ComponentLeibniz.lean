module

public import SerrePositivity.EInfinity.SimplexCuts.PositiveIntegerLeibniz
public import SerrePositivity.EInfinity.SimplexCuts.NullaryAction
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
# 切断成分の全 arity・全整数での Leibniz 則

Berger–Fresse §2.2.7、M14 L10。
正 arity の切断和と、零 arity の同じ空語 augmentation・AW 余単位を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable (A : Type u) [CommRing A]

/-- 元の切断和の全整数成分。零 arity は指定した空語と AW の余単位。 -/
def component (S : SSet.{0}) : (r : ℕ) → (i j t : ℤ) → (h : i + j = t) →
    (Surjection.complex A r).X i →ₗ[A] (chains A S).X j →ₗ[A]
      (power (chains A S) r).X t
  | 0, i, j, t, h => TensorProduct.curry
      (ιTensorObj (Surjection.complex A 0) (chains A S) i j t h ≫
        (nullaryAction A S).f t).hom
  | r + 1, i, j, t, h => positiveIntegerBilinear A S r i j t h

/-- L10：同じ切断成分は、全 arity・全整数で元の二つの微分と両立する。 -/
lemma component_d (S : SSet.{0}) (r : ℕ) (i j : ℤ)
    (a : (Surjection.complex A r).X i) (b : (chains A S).X j) :
    (power (chains A S) r).d (i + j) (i + j + 1)
        (component A S r i j (i + j) rfl a b) =
      component A S r (i + 1) j (i + j + 1) (by omega)
        ((Surjection.complex A r).d i (i + 1) a) b +
      i.negOnePow • component A S r i (j + 1) (i + j + 1) (by omega) a
        ((chains A S).d j (j + 1) b) := by
  cases r with
  | zero =>
    exact ConcreteCategory.congr_hom (tensorComponent_d (nullaryAction A S) i j) (a ⊗ₜ[A] b)
  | succ r => exact positiveIntegerBilinear_d A S r i j a b

end SerrePositivity.EInfinity.SimplexCuts

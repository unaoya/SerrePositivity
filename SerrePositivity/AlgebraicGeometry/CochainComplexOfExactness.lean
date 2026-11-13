module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：具体的な微分で与えた非負次数の加群複体の完全性を Acyclic にまとめる。
方針：零次は最初の微分の単射性、正次数は Function.Exact を使う。
規約：基底環の宇宙と加群の宇宙は独立。
使われ方：F8 の明示的な増大全複体の acyclicity。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]

/-- 最初の微分が単射で、連続する微分がすべて完全なら、作った複体は acyclic。 -/
theorem cochainComplexOf_acyclic_of_injective_exact
    (X : ℕ → ModuleCat.{u} R) (d : ∀ n, X n ⟶ X (n + 1))
    (hdd : ∀ n, d n ≫ d (n + 1) = 0)
    (hinj : Function.Injective (d 0).hom)
    (hexact : ∀ n, Function.Exact (d n).hom (d (n + 1)).hom) :
    (CochainComplex.of X d hdd).Acyclic := by
  let K := CochainComplex.of X d hdd
  intro q
  cases q with
  | zero =>
    rw [K.exactAt_iff' 0 0 1 (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    change Function.Exact (K.d 0 0).hom (K.d 0 1).hom
    rw [K.shape 0 0 (by simp)]
    change Function.Exact (0 : X 0 →ₗ[R] X 0)
      (CochainComplex.of.d X d 0 (0 + 1)).hom
    rw [CochainComplex.of_d]
    exact (LinearMap.exact_zero_iff_injective (X 0) (d 0).hom).mpr hinj
  | succ n =>
    rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)]
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    change Function.Exact (K.d n (n + 1)).hom (K.d (n + 1) (n + 2)).hom
    change Function.Exact (CochainComplex.of.d X d n (n + 1)).hom
      (CochainComplex.of.d X d (n + 1) (n + 1 + 1)).hom
    rw [CochainComplex.of_d, CochainComplex.of_d]
    exact hexact n

end SerrePositivity.AlgebraicGeometry

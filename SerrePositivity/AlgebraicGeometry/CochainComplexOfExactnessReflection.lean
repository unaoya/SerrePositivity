module

public import SerrePositivity.AlgebraicGeometry.CochainComplexOfExactness

/-!
概要：明示的な非負次数の加群複体の完全性から、微分の完全性を取り出す。
方針：既存の完全性判定の逆向きとして、零次と正次数の短複体を読む。
規約：係数環と加群の宇宙は独立。
使われ方：増大全複体の共通細分による比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]

/-- 明示的な複体の完全性から、最初の微分の単射性と以後の完全性を取り出す。 -/
theorem cochainComplexOf_injective_exact_of_acyclic
    (X : ℕ → ModuleCat.{u} R) (d : ∀ n, X n ⟶ X (n + 1))
    (hdd : ∀ n, d n ≫ d (n + 1) = 0)
    (hK : (CochainComplex.of X d hdd).Acyclic) :
    Function.Injective (d 0).hom ∧
      ∀ n, Function.Exact (d n).hom (d (n + 1)).hom := by
  let K := CochainComplex.of X d hdd
  constructor
  · have h := hK 0
    rw [K.exactAt_iff' 0 0 1 (by simp) (by simp)] at h
    have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h
    change Function.Exact (K.d 0 0).hom (K.d 0 1).hom at he
    rw [K.shape 0 0 (by simp)] at he
    change Function.Exact (0 : X 0 →ₗ[R] X 0)
      (CochainComplex.of.d X d 0 (0 + 1)).hom at he
    rw [CochainComplex.of_d] at he
    exact (LinearMap.exact_zero_iff_injective (X 0) (d 0).hom).mp he
  · intro n
    have h := hK (n + 1)
    rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)] at h
    have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h
    change Function.Exact (K.d n (n + 1)).hom (K.d (n + 1) (n + 2)).hom at he
    change Function.Exact (CochainComplex.of.d X d n (n + 1)).hom
      (CochainComplex.of.d X d (n + 1) (n + 1 + 1)).hom at he
    rw [CochainComplex.of_d, CochainComplex.of_d] at he
    exact he

end SerrePositivity.AlgebraicGeometry

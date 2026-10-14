module

public import SerrePositivity.CommutativeAlgebra.CoefficientEvalDerivation
public import SerrePositivity.CommutativeAlgebra.ModuleDerivationDescent
public import SerrePositivity.FieldTheory.PAdjoin
public import Mathlib.RingTheory.Adjoin.PowerBasis

/-! # p乗根の関係式を消す加群値導分の延長

係数の導分を多項式へ移し、実際の評価の核を消すことを確認して降下する。
添加した生成元を0に送り、底体上の元の導分を保持する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open Polynomial
variable {R K L V : Type*} [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [AddCommGroup V] [Module R V] [Module K V] [Module L V]
  [IsScalarTower R K V] [IsScalarTower R L V] [IsScalarTower K L V]

/-- 非自明なp乗根が終域を生成するとき、関係式の係数を消す導分は実際に延長できる。 -/
theorem exists_derivation_primeRoot_extension
    {p : ℕ} [Fact p.Prime] [CharP L p] (x : L) (a : K)
    (hpow : x ^ p = algebraMap K L a) (hx : x ∉ Set.range (algebraMap K L))
    (hs : Algebra.adjoin K {x} = ⊤) (δ : Derivation R K V) (hδa : δ a = 0) :
    ∃ Δ : Derivation R L V, (∀ c : K, Δ (algebraMap K L c) = δ c) ∧ Δ x = 0 := by
  let : Algebra K[X] L := (aeval x).toRingHom.toAlgebra
  let : Module K[X] V := Module.compHom V (aeval x).toRingHom
  let : IsScalarTower K[X] L V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower R K[X] L := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R L r = aeval x (C (algebraMap R K r))
    rw [aeval_C, IsScalarTower.algebraMap_apply R K L]
  let d : Derivation R K[X] V :=
    { toLinearMap := coefficientEvalLinearMap x δ
      map_one_eq_zero' := by simpa only [← C_1, coefficientEvalLinearMap_C] using δ.map_one_eq_zero
      leibniz' := fun f g ↦ coefficientEvalLinearMap_leibniz x δ f g }
  have hdx : d X = 0 := coefficientEvalLinearMap_X x δ
  have hdc (c : K) : d (C c) = δ c := coefficientEvalLinearMap_C x δ c
  have hdm : d (minpoly K x) = 0 := by
    rw [minpoly_eq_X_pow_sub_C_of_pow_eq x a hpow hx, map_sub, hdc, hδa]
    simp only [d.leibniz_pow, hdx, smul_zero, sub_zero]
  have hf : Function.Surjective (algebraMap K[X] L) := by
    let B := PowerBasis.ofAdjoinEqTop (isIntegral_of_prime_pow_eq x a hpow) hs
    intro y
    obtain ⟨f, hf⟩ := B.exists_eq_aeval' y
    refine ⟨f, ?_⟩
    change aeval x f = y
    simpa only [B, PowerBasis.ofAdjoinEqTop_gen] using hf.symm
  have hd : ∀ f, algebraMap K[X] L f = 0 → d f = 0 := by
    intro f hf
    obtain ⟨g, rfl⟩ := minpoly.dvd_iff.mpr hf
    rw [d.leibniz, hdm, smul_zero, add_zero]
    change aeval x (minpoly K x) • d g = 0
    rw [minpoly.aeval, zero_smul]
  refine ⟨descendModuleDerivation hf d hd, ?_, ?_⟩
  · intro c
    rw [← show algebraMap K[X] L (C c) = algebraMap K L c from aeval_C x c,
      descendModuleDerivation_apply, hdc]
  · rw [← show algebraMap K[X] L X = x from aeval_X x,
      descendModuleDerivation_apply, hdx]

end SerrePositivity

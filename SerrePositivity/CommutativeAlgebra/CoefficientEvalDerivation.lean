module

public import Mathlib.RingTheory.Derivation.MapCoeffs

/-! # 係数の導分を多項式に適用して評価する

変数を定数として扱う係数導分を、指定した評価点で加群値の線形写像へ移す。
Mathlibの係数導分・多項式加群の評価を再利用する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open Polynomial
variable {R K L V : Type*} [CommRing R] [CommRing K] [CommRing L]
  [Algebra R K] [Algebra R L] [Algebra K L]
  [AddCommGroup V] [Module R V] [Module K V] [Module L V]
  [IsScalarTower R K V] [IsScalarTower R L V] [IsScalarTower K L V]

/-- 係数の導分を取り、変数をxに評価するR線形写像。 -/
def coefficientEvalLinearMap (x : L) (δ : Derivation R K V) : K[X] →ₗ[R] V := by
  let : IsScalarTower R K (PolynomialModule L V) :=
    IsScalarTower.of_algebraMap_smul fun r m ↦ by
      ext n
      exact IsScalarTower.algebraMap_smul K r (m.coeff n)
  exact ((PolynomialModule.eval x).restrictScalars R).comp
    (((PolynomialModule.map L (LinearMap.id : V →ₗ[K] V)).restrictScalars R).comp
      δ.mapCoeffs.toLinearMap)

omit [Algebra K L] [IsScalarTower K L V] in
@[simp] theorem coefficientEvalLinearMap_C (x : L) (δ : Derivation R K V) (a : K) :
    coefficientEvalLinearMap x δ (C a) = δ a := by
  simp [coefficientEvalLinearMap]

omit [Algebra K L] [IsScalarTower K L V] in
@[simp] theorem coefficientEvalLinearMap_X (x : L) (δ : Derivation R K V) :
    coefficientEvalLinearMap x δ X = 0 := by
  simp [coefficientEvalLinearMap]

/-- 係数導分の評価は、同じ評価写像による作用についてLeibniz則を満たす。 -/
theorem coefficientEvalLinearMap_leibniz (x : L) (δ : Derivation R K V) (f g : K[X]) :
    coefficientEvalLinearMap x δ (f * g) =
      aeval x f • coefficientEvalLinearMap x δ g +
        aeval x g • coefficientEvalLinearMap x δ f := by
  change (PolynomialModule.eval x) ((PolynomialModule.map L LinearMap.id)
    (δ.mapCoeffs (f * g))) = _
  rw [δ.mapCoeffs.leibniz, map_add, map_add, PolynomialModule.map_smul,
    PolynomialModule.map_smul, PolynomialModule.eval_smul, PolynomialModule.eval_smul]
  simp only [Polynomial.eval_map, Polynomial.aeval_def, coefficientEvalLinearMap,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rfl

end SerrePositivity

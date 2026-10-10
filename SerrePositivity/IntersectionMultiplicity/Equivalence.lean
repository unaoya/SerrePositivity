module

public import SerrePositivity.IntersectionMultiplicity.Basic
public import SerrePositivity.HomologicalAlgebra.TorSymmetry

/-! # 交点重複度の同型不変性と対称性

Tor の関手性と変数交換の線形同値から長さの等式を得て、交代和へ移す。
有限生成性・正則性・有限長性を使わず、`chi` の定義に対して成り立つ。
-/

public section

universe u

namespace SerrePositivity

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- 交点重複度は両変数の線形同値で不変。 -/
theorem chi_congr
    {M M' N N' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (e : M ≃ₗ[R] M') (e' : N ≃ₗ[R] N') : chi R M N = chi R M' N' := by
  apply finsum_congr
  intro i
  congr 2
  let eTor := (((Tor (ModuleCat R) i).mapIso e.toModuleIso).app (ModuleCat.of R N)) ≪≫
    (((Tor (ModuleCat R) i).obj (ModuleCat.of R M')).mapIso e'.toModuleIso)
  exact congrArg ENat.toNat eTor.toLinearEquiv.length_eq

/-- 交点重複度は二つの加群の交換で不変。 -/
theorem chi_comm (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : chi R M N = chi R N M := by
  apply finsum_congr
  intro i
  congr 2
  exact congrArg ENat.toNat (torComm i (ModuleCat.of R M) (ModuleCat.of R N)).length_eq

end SerrePositivity

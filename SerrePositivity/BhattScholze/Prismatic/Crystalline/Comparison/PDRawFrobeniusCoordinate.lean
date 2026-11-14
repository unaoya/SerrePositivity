module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyZero
public import Mathlib.Algebra.CharP.Lemmas
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CohomologyZero

/-!
# pd Čech 模型での Frobenius 座標の差

## 概要
整係数の Frobenius 座標の余面微分は p で割り切れる。

## 方針
二つの頂点の差は分冪座標で、その p 乗は p の階乗の倍数。

## 規約
余面の順序は第 1 頂点から第 0 頂点を引く。

## 使われ方
Bockstein の余鎖の持ち上げ。
-/

public noncomputable section

open CategoryTheory DividedPowerAlgebra SerrePositivity.Cosimplicial
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] (r : ℕ)

private theorem pdDiff_pow_dvd (n : SimplexCategory) (x : Diff k r n) :
    (p : pdRaw k r n.len) ∣ (pdDiff k r n x) ^ p := by
  let f : DividedPowerAlgebra k (Diff k r n) →ₐ[k] pdRaw k r n.len :=
    Algebra.TensorProduct.includeRight
  have h := congrArg f (DividedPowerAlgebra.natFactorial_mul_dp_eq (R := k) p x)
  change f ((p.factorial : DividedPowerAlgebra k (Diff k r n)) * dp k p x) =
    f ((dp k 1 x) ^ p) at h
  rw [map_mul, map_natCast, map_pow] at h
  change (p.factorial : pdRaw k r n.len) * f (dp k p x) = (pdDiff k r n x)^p at h
  rw [← h]
  obtain ⟨a, ha⟩ := Nat.dvd_factorial (Fact.out : p.Prime).pos (le_refl p)
  refine ⟨(a : pdRaw k r n.len) * f (dp k p x), ?_⟩
  rw [← mul_assoc, ← Nat.cast_mul, ← ha]

private theorem copy_pow_sub_dvd (j : Fin r) :
    (p : pdRaw k r 1) ∣ copy k r ⦋1⦌ j 1 ^ p - copy k r ⦋1⦌ j 0 ^ p := by
  have h₀ : copy k r ⦋1⦌ j 0 = baseVar k r ⦋1⦌ j := by
    simp [copy, vertexDiff]
  rw [h₀, copy, add_comm]
  exact Nat.Prime.dvd_add_pow_sub_pow_of_dvd (pdDiff k r ⦋1⦌ (vertexDiff k r ⦋1⦌ j 1))
    (baseVar k r ⦋1⦌ j) (Fact.out : p.Prime)
    (pdDiff_pow_dvd p k r _ _) (dvd_mul_right _ _)

/-- 第 0 頂点の Frobenius 座標の整係数での持ち上げ。 -/
def pdRawFrobeniusCoordinate (j : Fin r) :
    (pdRawModel k r ⋙ Under.forget (CommRingCat.of k)).obj ⦋0⦌ :=
  copy k r ⦋0⦌ j 0 ^ p

/-- 第 0 頂点の座標の p 乗を余面微分した値は p で割り切れる。 -/
theorem pdRaw_frobeniusCoordinate_dvd (j : Fin r) :
    (p : (pdRawModel k r ⋙ Under.forget (CommRingCat.of k)).obj ⦋1⦌) ∣ cochainDifferential
      (pdRawModel k r ⋙ Under.forget (CommRingCat.of k)) 0 (pdRawFrobeniusCoordinate p k r j) := by
  rw [cochainDifferential_zero]
  change (p : pdRaw k r 1) ∣
    pdRawMap k r (SimplexCategory.δ (0 : Fin 2)) (copy k r ⦋0⦌ j 0 ^ p) -
      pdRawMap k r (SimplexCategory.δ (1 : Fin 2)) (copy k r ⦋0⦌ j 0 ^ p)
  rw [map_pow, map_pow, pdRawMap_copy, pdRawMap_copy]
  exact copy_pow_sub_dvd p k r j

end SerrePositivity.BhattScholze.Prismatic

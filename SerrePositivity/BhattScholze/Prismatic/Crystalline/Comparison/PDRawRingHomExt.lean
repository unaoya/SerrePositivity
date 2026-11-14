module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDFrobeniusLift
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDFrobeniusLift

/-!
# p 正則な標的への小さい分冪模型の射の一意性

## 概要
p 正則で素数以外の自然数が可逆な標的への代数射は、各頂点の変数像で決まる。

## 方針
階乗を掛けて分冪生成元を通常の冪に直し、標的で階乗を消去する。

## 規約
標的の p 正則性と p 局所性を型に明記する。

## 使われ方
BS 著者版 Theorems 5.2・6.4 の小さい結晶比較と δ 除算模型からの射の照合。
-/

public noncomputable section

open Algebra.TensorProduct
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] {k T : Type u} [CommRing k] [CommRing T] [Algebra k T]
variable (r n : ℕ) (hreg : Function.Injective (fun x : T => (p : T) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : T))
variable (f g : pdRaw k r n →ₐ[k] T)
variable (hv : ∀ j : Fin r, ∀ i : Fin (n + 1),
  f (PDSmallRawEnvelope.unit r n (MvPolynomial.X (ULift.up j, i))) =
    g (PDSmallRawEnvelope.unit r n (MvPolynomial.X (ULift.up j, i))))

include hreg hlocal hv in
private theorem raw_ext : f = g := by
  have hcopy (j : Fin r) (i : Fin (n + 1)) :
      f (copy k r ⦋n⦌ j i) = g (copy k r ⦋n⦌ j i) := by
    simpa only [PDSmallRawEnvelope.unit_X] using hv j i
  have hbase (j : Fin r) : f (baseVar k r ⦋n⦌ j) = g (baseVar k r ⦋n⦌ j) := by
    simpa only [copy, vertexDiff, Fin.cases_zero, map_zero, add_zero] using hcopy j 0
  have hlin : f.toLinearMap.comp (pdDiff k r ⦋n⦌) =
      g.toLinearMap.comp (pdDiff k r ⦋n⦌) := by
    apply (Finsupp.basisSingleOne (R := k)).ext
    rintro ⟨j, i⟩
    change f (pdDiff k r ⦋n⦌ (Finsupp.single (j, i) 1)) =
      g (pdDiff k r ⦋n⦌ (Finsupp.single (j, i) 1))
    have h := hcopy j i.succ
    simpa only [copy, map_add, hbase, vertexDiff, Fin.cases_succ, add_right_inj] using h
  apply Algebra.TensorProduct.ext
  · exact MvPolynomial.algHom_ext hbase
  · let inc : DividedPowerAlgebra k ((Fin r × Fin n) →₀ k) →ₐ[k] pdRaw k r n := includeRight
    change f.comp inc = g.comp inc
    apply DividedPowerAlgebra.algHom_ext
    intro m x
    change f (inc (DividedPowerAlgebra.dp k m x)) = g (inc (DividedPowerAlgebra.dp k m x))
    apply factorial_regular hreg hlocal m
    have hm : (m.factorial : pdRaw k r n) * inc (DividedPowerAlgebra.dp k m x) =
        (inc (DividedPowerAlgebra.dp k 1 x)) ^ m := by
      simpa only [map_mul, map_natCast, map_pow] using
        congrArg inc (DividedPowerAlgebra.natFactorial_mul_dp_eq m x)
    have hx : f (inc (DividedPowerAlgebra.dp k 1 x)) =
        g (inc (DividedPowerAlgebra.dp k 1 x)) := DFunLike.congr_fun hlin x
    have hf := congrArg f hm
    have hg := congrArg g hm
    simp only [map_mul, map_natCast, map_pow] at hf hg
    exact hf.trans ((congrArg (fun z => z ^ m) hx).trans hg.symm)

include hreg hlocal hv

/-- p 正則で p 局所な標的への代数射は、各頂点の初期座標で比較できる。 -/
theorem pdRawAlgHom_ext_of_primeRegular : f = g :=
  raw_ext p r n hreg hlocal f g hv

end SerrePositivity.BhattScholze.Prismatic

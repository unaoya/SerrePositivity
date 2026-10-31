module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Quotient.Defs
/-!
概要：固定した自由加群の商で各次数を表示する複体の小さいコード型を与える。
方針：関係部分加群と商上の微分を保持し、既存の CochainComplex.of で評価する。
規約：任意の Type u の台をフィールドに持たず、固定基底上の関係だけを動かす。
使われ方：16時間試作で、出発 dg 圏の提示ラベル自体を Type u に保つ基盤。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (B : Type u)

structure DGComplexPresentationCode where
  relations : ℤ → Submodule R (B →₀ R)
  differential : ∀ n : ℤ, ModuleCat.of R ((B →₀ R) ⧸ relations n) ⟶
    ModuleCat.of R ((B →₀ R) ⧸ relations (n + 1))
  square : ∀ n, differential n ≫ differential (n + 1) = 0

namespace DGComplexPresentationCode

def value (c : DGComplexPresentationCode R B) : Complex R :=
  CochainComplex.of (fun n => ModuleCat.of R ((B →₀ R) ⧸ c.relations n))
    c.differential c.square

lemma small : Small.{u} (DGComplexPresentationCode R B) := inferInstance

end DGComplexPresentationCode
end SerrePositivity.DifferentialGraded

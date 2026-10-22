module
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingCochainUnitLaws
public import Mathlib.CategoryTheory.Monoidal.Mon
/-!
概要：任意の非可換単体環から得る実 dg 代数。
方針：同じ正規化複体・shuffle 乗法・単位を Mon(Complex) に包装する。
規約：可換性や平坦性を仮定しない。使われ方：β5(g) の正規化関手の対象。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable (A : SimplicialObject RingCat.{u})
local notation "P" => simplicialRingNormalizedDGComplex A
local notation "mu" => simplicialRingDGCochainMultiplication A
local notation "eta" => simplicialRingDGCochainUnit A
def simplicialRingNormalizedDGAlgebra :
    Mon (DifferentialGraded.Complex simplicialRingCoefficient.{u}) where
  X := P
  mon :=
    { one := eta
      mul := mu
      one_mul := simplicialRingDGCochainMultiplication_left_unit A
      mul_one := simplicialRingDGCochainMultiplication_right_unit A
      mul_assoc := simplicialRingDGCochainMultiplication_assoc A }
lemma simplicialRingNormalizedDGAlgebra_X :
    (simplicialRingNormalizedDGAlgebra A).X = P := rfl
lemma simplicialRingNormalizedDGAlgebra_one :
    MonObj.one (X := (simplicialRingNormalizedDGAlgebra A).X) = eta := rfl
lemma simplicialRingNormalizedDGAlgebra_mul :
    MonObj.mul (X := (simplicialRingNormalizedDGAlgebra A).X) = mu := rfl
end SerrePositivity.InfinityCategories

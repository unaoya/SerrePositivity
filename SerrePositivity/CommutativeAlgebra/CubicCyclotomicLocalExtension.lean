module

public import SerrePositivity.CommutativeAlgebra.CubicCyclotomicLocalFiber
public import SerrePositivity.CommutativeAlgebra.FlatLocalDimension
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.Submodule

/-! # The flat local cubic cyclotomic extension and its regularity -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open Polynomial IsLocalRing
variable {R : Type u} [CommRing R] [IsLocalRing R]
    (g h : (ResidueField R)[X])
    (hf : cubicCyclotomicPolynomial (ResidueField R) = g * h)
    [Fact (Irreducible g)]

/-- The actual local extension at the selected factor point. -/
abbrev CubicCyclotomicLocalRing := Localization.AtPrime (cubicCyclotomicFactorPoint g h hf)

instance cubicCyclotomicLocalRing_algebra : Algebra R (CubicCyclotomicLocalRing g h hf) :=
  ((algebraMap (CubicCyclotomicAlgebra R) (CubicCyclotomicLocalRing g h hf)).comp
    (algebraMap R (CubicCyclotomicAlgebra R))).toAlgebra

-- Fix the scalar actions to those of the structural algebras when composing the tower.
local instance cubicCyclotomicSourceSMul : SMul R (CubicCyclotomicAlgebra R) :=
  (inferInstance : Algebra R (CubicCyclotomicAlgebra R)).toSMul
local instance cubicCyclotomicTargetSMul :
    SMul (CubicCyclotomicAlgebra R) (CubicCyclotomicLocalRing g h hf) :=
  (inferInstance : Algebra (CubicCyclotomicAlgebra R) (CubicCyclotomicLocalRing g h hf)).toSMul
local instance cubicCyclotomicBaseSMul : SMul R (CubicCyclotomicLocalRing g h hf) :=
  (inferInstance : Algebra R (CubicCyclotomicLocalRing g h hf)).toSMul

instance cubicCyclotomicLocalRing_scalarTower :
    IsScalarTower R (CubicCyclotomicAlgebra R) (CubicCyclotomicLocalRing g h hf) :=
  IsScalarTower.of_algebraMap_eq' (R := R) (S := CubicCyclotomicAlgebra R)
    (A := CubicCyclotomicLocalRing g h hf) rfl

instance cubicCyclotomicLocalRing_isLocal : IsLocalRing (CubicCyclotomicLocalRing g h hf) :=
  inferInstance

instance cubicCyclotomicLocalRing_noetherian [IsNoetherianRing R] :
    IsNoetherianRing (CubicCyclotomicLocalRing g h hf) :=
  IsLocalization.isNoetherianRing (cubicCyclotomicFactorPoint g h hf).primeCompl _ inferInstance

local instance cubicCyclotomicBaseModule : Module R (CubicCyclotomicLocalRing g h hf) :=
  Algebra.toModule

instance cubicCyclotomicLocalRing_flat : Module.Flat R (CubicCyclotomicLocalRing g h hf) := by
  let : Module.Flat (CubicCyclotomicAlgebra R) (CubicCyclotomicLocalRing g h hf) :=
    IsLocalization.flat _ (cubicCyclotomicFactorPoint g h hf).primeCompl
  exact Module.Flat.trans R (CubicCyclotomicAlgebra R) (CubicCyclotomicLocalRing g h hf)

lemma cubicCyclotomicLocalRing_map_maximalIdeal (hc : IsCoprime g h) :
    (maximalIdeal R).map (algebraMap R (CubicCyclotomicLocalRing g h hf)) =
      maximalIdeal (CubicCyclotomicLocalRing g h hf) :=
  cubicCyclotomicLocal_map_maximalIdeal g h hf _ hc

/-- The root in the same local model used for every preservation theorem. -/
def cubicCyclotomicLocalRoot : CubicCyclotomicLocalRing g h hf :=
  algebraMap (CubicCyclotomicAlgebra R) (CubicCyclotomicLocalRing g h hf) (cubicCyclotomicRoot R)

lemma cubicCyclotomicLocalRoot_relation :
    cubicCyclotomicLocalRoot g h hf ^ 2 + cubicCyclotomicLocalRoot g h hf + 1 = 0 := by
  have he := congrArg (algebraMap (CubicCyclotomicAlgebra R) (CubicCyclotomicLocalRing g h hf))
    (cubicCyclotomicRoot_relation R)
  rw [map_add, map_add, map_pow, map_one, map_zero] at he
  exact he

lemma cubicCyclotomicLocalRoot_cube : cubicCyclotomicLocalRoot g h hf ^ 3 = 1 :=
  cube_eq_one_of_cubic_relation _ (cubicCyclotomicLocalRoot_relation g h hf)

lemma cubicCyclotomicLocalRing_three_isUnit (htwo : (2 : ResidueField R) = 0) :
    IsUnit (3 : CubicCyclotomicLocalRing g h hf) := by
  simpa only [map_ofNat] using (isUnit_three_of_residue_two_eq_zero htwo).map
    (algebraMap R (CubicCyclotomicLocalRing g h hf))

lemma cubicCyclotomicLocalRoot_units (htwo : (2 : ResidueField R) = 0) :
    IsUnit (1 - cubicCyclotomicLocalRoot g h hf) ∧
      IsUnit (1 - cubicCyclotomicLocalRoot g h hf ^ 2) :=
  isUnit_one_sub_of_cubic_relation _ (cubicCyclotomicLocalRoot_relation g h hf)
    (cubicCyclotomicLocalRing_three_isUnit g h hf htwo)

lemma cubicCyclotomicLocalRing_dimension [IsNoetherianRing R] (hc : IsCoprime g h) :
    ringKrullDim (CubicCyclotomicLocalRing g h hf) = ringKrullDim R :=
  ringKrullDim_eq_of_flat_of_map_maximalIdeal R _
    (cubicCyclotomicLocalRing_map_maximalIdeal g h hf hc)

-- The selected residue factor and local model retain their original local-ring index.
set_option linter.overlappingInstances false in
lemma cubicCyclotomicLocalRing_regular [IsRegularLocalRing R] (hc : IsCoprime g h) :
    IsRegularLocalRing (CubicCyclotomicLocalRing g h hf) :=
  isRegularLocalRing_of_flat_of_map_maximalIdeal R _
    (cubicCyclotomicLocalRing_map_maximalIdeal g h hf hc)

end SerrePositivity

module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 小さいperfect dg代表系の全HomとH⁰同値の受入検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : Small.{u} (SmallPerfectDGModuleOver A D S) := inferInstance
example (S : Set D) : DGCategory A (SmallPerfectDGModuleOver A D S) := inferInstance
example (S : Set D) (M N : SmallPerfectDGModuleOver A D S) :
    (M ⟶[Complex A] N) = moduleHom A D M.val.val N.val.val := rfl
example (S : Set D) (M N : SmallPerfectDGModuleOver A D S) (n : ℤ) :
    (M ⟶[Complex A] N).d n (n + 1) = (moduleHom A D M.val.val N.val.val).d n (n + 1) := rfl
example (S : Set D) : (smallPerfectDGModuleToPerfect A D S).IsEquivalence := inferInstance
example (S : Set D) : (smallPerfectDGModuleToPerfect A D S).Linear A := inferInstance
example (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).inverse.Linear A := inferInstance
example (S : Set D) :
    (smallPerfectDGModuleHomotopyEquivalence A D S).inverse.Additive := inferInstance
example (S : Set D) : QuasiEquivalence (smallPerfectDGModuleInclusion A D S) :=
  smallPerfectDGModuleInclusion_quasiEquivalence A D S
example : Small.{0} (SmallPerfectDGModuleOver (ZMod 2) PUnit.{1} Set.univ) := inferInstance
example : (smallPerfectDGModuleToPerfect (ZMod 2) PUnit.{1} ∅).IsEquivalence := inferInstance

#print axioms perfectDGModuleRepresentative
#print axioms smallPerfectDGModuleOverSmall
#print axioms smallPerfectDGModuleInclusion
#print axioms smallPerfectDGModuleInclusionHomotopyFull
#print axioms smallPerfectDGModuleInclusionHomotopyFaithful
#print axioms smallPerfectDGModuleToPerfect
#print axioms smallPerfectDGModuleToPerfectFull
#print axioms smallPerfectDGModuleToPerfectFaithful
#print axioms smallPerfectDGModuleObject
#print axioms smallPerfectDGModuleObject_comparison
#print axioms smallPerfectDGModuleToPerfectEssSurj
#print axioms smallPerfectDGModuleToPerfectIsEquivalence
#print axioms smallPerfectDGModuleHomotopyEquivalence
#print axioms smallPerfectDGModuleToPerfectLinear
#print axioms smallPerfectDGModuleToPerfectAdditive
#print axioms smallPerfectDGModuleInclusionHomotopyEssSurj
#print axioms smallPerfectDGModuleInclusion_quasiEquivalence
#print axioms smallPerfectDGModuleHomotopyEquivalenceFunctorLinear

#print axioms smallPerfectDGModuleEnrichment
#print axioms smallPerfectDGModuleHomotopyEquivalenceFunctorAdditive

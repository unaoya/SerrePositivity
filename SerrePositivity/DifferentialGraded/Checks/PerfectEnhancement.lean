module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 主Hom endを持つ射影的perfect加群とH⁰の線形同値 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) : DGCategory A (PerfectDGModuleOver A D S) := inferInstance
example (S : Set D) (M N : PerfectDGModuleOver A D S) :
    (M ⟶[Complex A] N) = moduleHom A D M.val N.val := rfl
example (S : Set D) (M N : PerfectDGModuleOver A D S) (n : ℤ) :
    (M ⟶[Complex A] N).d n (n + 1) = (moduleHom A D M.val N.val).d n (n + 1) := rfl

example (S : Set D) : (perfectDGModuleToPerfect A D S).Full := inferInstance
example (S : Set D) : (perfectDGModuleToPerfect A D S).Faithful := inferInstance
example (S : Set D) : (perfectDGModuleToPerfect A D S).EssSurj := inferInstance
example (S : Set D) : (perfectDGModuleToPerfect A D S).Linear A := inferInstance
example (S : Set D) : (perfectDGModuleHomotopyEquivalence A D S).inverse.Linear A := inferInstance
example (S : Set D) : (perfectDGModuleHomotopyEquivalence A D S).inverse.Additive := inferInstance

example (S : Set D) (X : PerfectModuleCategoryOver A D S) :
    ∃ M : PerfectDGHomotopyCategoryOver A D S,
      Nonempty ((perfectDGModuleToPerfect A D S).obj M ≅ X) :=
  Functor.EssSurj.mem_essImage (perfectDGModuleToPerfect A D S) X

example : (perfectDGModuleToPerfect (ZMod 2) PUnit.{1} Set.univ).IsEquivalence := inferInstance
example : (perfectDGModuleHomotopyEquivalence (ZMod 2) PUnit.{1} ∅).inverse.Linear (ZMod 2) :=
  inferInstance

#print axioms dgFullSubcategoryEnrichment
#print axioms dgFullSubcategoryInclusion
#print axioms dgFullSubcategoryInclusionClosedFull
#print axioms dgFullSubcategoryInclusionClosedFaithful
#print axioms dgFullSubcategoryInclusion_boundary_iff
#print axioms dgFullSubcategoryInclusion_onHomotopy_map
#print axioms dgFullSubcategoryInclusionHomotopyFull
#print axioms dgFullSubcategoryInclusionHomotopyFaithful
#print axioms moduleHomotopyToDerivedClosedLinear
#print axioms modulePerfectProjectiveOver
#print axioms perfectDGModuleInclusion
#print axioms perfectDGModuleInclusionHomotopyFull
#print axioms perfectDGModuleInclusionHomotopyFaithful
#print axioms perfectDGModuleToDerived
#print axioms perfectDGModuleToDerived_obj_perfect
#print axioms perfectDGModuleToDerivedFull
#print axioms perfectDGModuleToDerivedFaithful
#print axioms perfectDGModuleToPerfect
#print axioms perfectDGModuleToPerfectFull
#print axioms perfectDGModuleToPerfectFaithful
#print axioms perfectDGModuleToPerfectEssSurj
#print axioms perfectDGModuleToPerfectIsEquivalence
#print axioms perfectDGModuleHomotopyEquivalence
#print axioms perfectDGModuleToDerivedAdditive
#print axioms perfectDGModuleToDerivedLinear
#print axioms perfectDGModuleToPerfectAdditive
#print axioms perfectDGModuleToPerfectLinear
#print axioms perfectDGModuleHomotopyEquivalenceFunctorAdditive
#print axioms perfectDGModuleHomotopyEquivalenceFunctorLinear
#print axioms perfectDGModuleToPerfectCompInclusion

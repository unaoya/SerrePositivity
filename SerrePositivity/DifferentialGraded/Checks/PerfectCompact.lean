module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # compact性のshift・三角閉性とPerf⇒compact -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Pretriangulated
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example : (moduleCompact A D).IsTriangulated := inferInstance
example : (moduleCompact A D).IsStableUnderShift ℤ := inferInstance
example {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) : moduleCompact A D X :=
  modulePerfect_compact A D hX
example {S : Set D} {X : DerivedModuleCategory A D} (hX : modulePerfectOver A D S X) :
    moduleCompact A D X := modulePerfectOver_compact A D hX

example {X : DerivedModuleCategory A D} (hX : moduleCompact A D X) (n : ℤ) :
    moduleCompact A D (X⟦n⟧) := moduleCompact_shift A D hX n

example (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (h₁ : moduleCompact A D T.obj₁) (h₂ : moduleCompact A D T.obj₂) :
    moduleCompact A D T.obj₃ := moduleCompact_triangle_obj₃ A D T hT h₁ h₂

example (X : DerivedModuleCategory (ZMod 2) PUnit.{1})
    (hX : modulePerfect (ZMod 2) PUnit.{1} X) : moduleCompact (ZMod 2) PUnit.{1} X :=
  modulePerfect_compact (ZMod 2) PUnit.{1} hX

#print axioms moduleCompact_equivalence
#print axioms moduleCompact_shift
#print axioms moduleCompactStableUnderShift
#print axioms moduleDerivedCoproductProjection
#print axioms moduleDerivedCoproductProjection_self
#print axioms moduleDerivedCoproductProjection_ne
#print axioms moduleDerivedCoproductFiniteProjection
#print axioms moduleDerivedCoproductFiniteProjection_mem
#print axioms moduleDerivedCoproductComplement_mem
#print axioms moduleCompactRange_ι
#print axioms moduleCompactRange_precompose
#print axioms moduleCompactRange_finiteProjection
#print axioms moduleCompact_triangle_obj₃
#print axioms moduleCompactTriangulatedClosed₃
#print axioms moduleCompactTriangulatedClosed₂
#print axioms moduleCompactContainsZero
#print axioms moduleCompactIsTriangulated
#print axioms moduleCompact_derivedShift
#print axioms moduleCompact_derivedBiprod
#print axioms moduleCompact_derivedCone
#print axioms ModuleFiniteCellCode.compact
#print axioms moduleFiniteCellOver_compact
#print axioms moduleFiniteCell_compact
#print axioms modulePerfectOver_compact
#print axioms modulePerfect_compact

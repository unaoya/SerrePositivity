module
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # finite cellの導来射・標準cone・Perfの厚い三角閉性 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Pretriangulated
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {P N : ModuleCategory A D} (hP : moduleHomotopicallyProjective A D P)
    (f : (moduleToDerived A D).obj P ⟶ (moduleToDerived A D).obj N) :
    ∃ g : P ⟶ N, (moduleToDerived A D).map g = f :=
  moduleProjectiveToDerived_map_surjective A D hP f

example (S : Set D) : IsTriangulated (PerfectModuleCategoryOver A D S) := inferInstance
example (S : Set D) : (perfectModuleInclusion A D S).IsTriangulated := inferInstance
example (S : Set D) : (finiteCellKaroubiFunctor A D S).IsTriangulated := inferInstance
example : (modulePerfect A D).IsStableUnderRetracts := inferInstance
example : (modulePerfect A D).IsTriangulated := inferInstance

example (S : Set D) (T : Triangle (DerivedModuleCategory A D))
    (hT : T ∈ distTriang (DerivedModuleCategory A D))
    (h₁ : modulePerfectOver A D S T.obj₁) (h₃ : modulePerfectOver A D S T.obj₃) :
    modulePerfectOver A D S T.obj₂ := modulePerfectOver_triangle_obj₂ A D S T hT h₁ h₃

example : IsTriangulated (PerfectModuleCategory (ZMod 2) PUnit.{1}) := inferInstance

#print axioms moduleProjectiveToDerived_map_surjective
#print axioms moduleDerivedConeTriangle
#print axioms moduleDerivedConeTriangle_distinguished
#print axioms derivedFiniteCellOverClosedUnderIso
#print axioms derivedFiniteCellOver_triangle_obj₃
#print axioms derivedFiniteCellOverTriangulatedClosed₃
#print axioms derivedFiniteCellOverTriangulatedClosed₂
#print axioms derivedFiniteCellOverContainsZero
#print axioms derivedFiniteCellOverIsTriangulated
#print axioms modulePerfectOver_triangle_obj₂
#print axioms modulePerfectOverTriangulatedClosed₂
#print axioms modulePerfectOverIsTriangulated
#print axioms modulePerfectIsTriangulated
#print axioms derivedFiniteCellInclusionIsTriangulated
#print axioms perfectModuleInclusionIsTriangulated
#print axioms finiteCellKaroubiFunctorIsTriangulated

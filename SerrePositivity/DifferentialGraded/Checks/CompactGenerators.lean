module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # 小さいcompact生成族と評価ホモロジーの零対象判定 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example : Small.{u} (Set.range (moduleCompactGenerators A D)) := moduleCompactGenerators_small A D
example (p : D × ℤ) : moduleCompact A D (moduleCompactGenerators A D p) :=
  moduleCompactGenerators_compact A D p
example (X : DerivedModuleCategory A D)
    (hX : ∀ p : D × ℤ, Subsingleton (moduleCompactGenerators A D p ⟶ X)) : IsZero X :=
  (moduleCompactGenerators_detect_zero A D X).mpr hX

example (N : ModuleCategory A D) :
    IsZero ((moduleToDerived A D).obj N) ↔ moduleAcyclic A D N :=
  moduleToDerived_isZero_iff_acyclic A D N

example (x : D) (N : ModuleCategory A D) :
    ((moduleEvaluation A D x).obj (N⟦(-3 : ℤ)⟧)).homology 0 ≅
      ((moduleEvaluation A D x).obj N).homology (-3) :=
  moduleEvaluationShiftHomologyIso A D x N (-3)

example (x : D) (N : ModuleCategory A D) :
    ((moduleEvaluation A D x).obj (N⟦(2 : ℤ)⟧)).homology 0 ≅
      ((moduleEvaluation A D x).obj N).homology 2 := moduleEvaluationShiftHomologyIso A D x N 2

example (X : DerivedModuleCategory (ZMod 2) PUnit.{1})
    (hX : ∀ p : PUnit.{1} × ℤ,
      Subsingleton (moduleCompactGenerators (ZMod 2) PUnit.{1} p ⟶ X)) : IsZero X :=
  (moduleCompactGenerators_detect_zero (ZMod 2) PUnit.{1} X).mpr hX

#print axioms moduleAcyclic_zeroTo_quasiIso
#print axioms moduleToDerived_isZero_of_acyclic
#print axioms moduleDerived_isZero_iff_homology
#print axioms moduleToDerived_isZero_iff_acyclic
#print axioms moduleEvaluationShiftHomologyIso
#print axioms moduleRepresentables_detect_zero
#print axioms moduleRepresentableShifts_detect_zero
#print axioms moduleCompactGenerators
#print axioms moduleCompactGenerators_small
#print axioms moduleCompactGenerators_compact
#print axioms moduleCompactGenerators_detect_zero

module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # U13d compact ⇔ Perf の型検証と公理監査 -/
@[expose] public section
noncomputable section
universe u v
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (X : DerivedModuleCategory A D) : moduleCompact A D X ↔ modulePerfect A D X :=
  moduleCompact_iff_perfect A D X

example (X : DerivedModuleCategory (ZMod 4) PUnit.{1})
    (hX : moduleCompact (ZMod 4) PUnit.{1} X) : modulePerfect (ZMod 4) PUnit.{1} X :=
  moduleCompact_perfect (ZMod 4) PUnit.{1} hX

#print axioms moduleFiniteCellFactorTarget_resolutionCandidate
#print axioms moduleFiniteCellFactorTarget_all
#print axioms moduleCompact_perfect
#print axioms moduleCompact_iff_perfect

module
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # finite cellの有限操作・指定生成元・有限support検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {S : Set D} {M : ModuleCategory A D} (c : ModuleFiniteCellCode A D S M) :
    ModuleFiniteCellCode A D (↑c.support : Set D) M := c.restrictSupport

example {S : Set D} {M : ModuleCategory A D} (c : ModuleFiniteCellCode A D S M) :
    (↑c.support : Set D) ⊆ S := c.support_subset

example {S : Set D} {M N : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) (d : ModuleFiniteCellCode A D S N) (f : M ⟶ N) :
    ModuleFiniteCellCode A D S (moduleCone A D f) := .cone c d f

example (x : D) (s : ℤ) : moduleFiniteCell A D
    ((ForgetEnrichment.of (Complex A) (representable A x))⟦s⟧) :=
  moduleFiniteCellOver_shift A D (moduleFiniteCell_representable A D x) s

example (x : PUnit.{1}) : moduleFiniteCell (ZMod 2) PUnit.{1}
    (ForgetEnrichment.of (Complex (ZMod 2)) (representable (ZMod 2) x)) :=
  moduleFiniteCell_representable (ZMod 2) PUnit.{1} x

#print axioms ModuleFiniteCellCode
#print axioms ModuleFiniteCellCode.mono
#print axioms ModuleFiniteCellCode.size
#print axioms ModuleFiniteCellCode.support
#print axioms ModuleFiniteCellCode.support_subset
#print axioms ModuleFiniteCellCode.restrictSupport
#print axioms moduleFiniteCellOver
#print axioms moduleFiniteCell
#print axioms moduleFiniteCellOver_mono
#print axioms moduleFiniteCellOver_iff_finite_generators
#print axioms moduleFiniteCellOver_zero
#print axioms moduleFiniteCellOver_representable
#print axioms moduleFiniteCellOver_shift
#print axioms moduleFiniteCellOver_biprod
#print axioms moduleFiniteCellOver_cone
#print axioms moduleFiniteCellOver_of_iso
#print axioms moduleFiniteCellOverClosedUnderIso
#print axioms moduleFiniteCell_representable
#print axioms moduleFiniteCell_iff_finite_generators

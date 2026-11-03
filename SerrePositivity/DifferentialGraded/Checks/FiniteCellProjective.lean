module
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # finite cellの主Hom射影性・反変shift・相対K-flat検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (M N : RightModule A D) :
    moduleHom A D (shiftModule 1 M) N ≅ (moduleHom A D M N)⟦(-1 : ℤ)⟧ :=
  moduleHomSourceShiftIso A D M N 1

example (F : DGFunctor A (RightModule A D)ᵒᵖ (Complex A)) (M : RightModule A D) (s : ℤ) :
    F.obj (op (shiftModule s M)) ≅ (F.obj (op M))⟦-s⟧ :=
  DGFunctor.moduleShiftOppImageIso A D F s M

example {S : Set D} {M : ModuleCategory A D} (c : ModuleFiniteCellCode A D S M) :
    moduleHomotopicallyProjective A D M := c.homotopicallyProjective A D

example {S : Set D} {M N : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) (d : ModuleFiniteCellCode A D S N) (f : M ⟶ N) :
    moduleHomotopicallyProjective A D (moduleCone A D f) :=
  (ModuleFiniteCellCode.cone c d f).homotopicallyProjective A D

example {M : ModuleCategory (ZMod 2) PUnit.{1}}
    (c : ModuleFiniteCellCode (ZMod 2) PUnit.{1} Set.univ M) :
    moduleRelativeKFlat (ZMod 2) PUnit.{1} (ForgetEnrichment.to (Complex (ZMod 2)) M) :=
  moduleFiniteCell_relativeKFlat (ZMod 2) PUnit.{1} ⟨c⟩

#print axioms complexShiftComparison
#print axioms complexShiftComparison_f
#print axioms complexShiftComparison_bijective
#print axioms complexShiftComparison_isIso
#print axioms complexShiftIso
#print axioms complexShiftIsoOfSumZero
#print axioms moduleShiftInElement_d
#print axioms DGFunctor.moduleShiftOppImageOut
#print axioms DGFunctor.moduleShiftOppImageIn
#print axioms DGFunctor.moduleShiftOppImageOut_d
#print axioms DGFunctor.moduleShiftOppImageOutIn
#print axioms DGFunctor.moduleShiftOppImageInOut
#print axioms DGFunctor.moduleShiftOppImageIso
#print axioms moduleHomSourceShiftIso
#print axioms moduleHomotopicallyProjective_shift
#print axioms moduleHomotopicallyProjective_cone
#print axioms moduleHomotopicallyProjective_biprod
#print axioms ModuleFiniteCellCode.homotopicallyProjective
#print axioms moduleFiniteCellOver_homotopicallyProjective
#print axioms moduleFiniteCell_homotopicallyProjective
#print axioms moduleFiniteCell_relativeKFlat

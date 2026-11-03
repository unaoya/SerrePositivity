module
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Data.ZMod.Basic

/-! # graded-split拡張のtensor保存と非有界coneの検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.BalancedTensor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) (L : LeftModule A D) :
    (tensorShortComplex A D s L).ShortExact :=
  tensorShortComplex_shortExact A D s L

example {M N : ModuleCategory A D} (f : M ⟶ N) (L : LeftModule A D) :
    Nonempty (((tensorShortComplex A D (moduleConeGradedSplit A D f) L).map
      (eval (ModuleCat.{u} A) (.up ℤ) (-1))).Splitting) :=
  ⟨tensorDegreeSplitting A D (moduleConeGradedSplit A D f) L (-1)⟩

example {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hP : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) P)) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N) :=
  moduleRelativeKFlat_of_gradedSplit A D s hM hP

example {M N : ModuleCategory (ZMod 2) PUnit.{1}} (f : M ⟶ N)
    (L : LeftModule (ZMod 2) PUnit.{1}) :
    (tensorShortComplex (ZMod 2) PUnit.{1}
      (moduleConeGradedSplit (ZMod 2) PUnit.{1} f) L).ShortExact :=
  tensorShortComplex_shortExact (ZMod 2) PUnit.{1}
    (moduleConeGradedSplit (ZMod 2) PUnit.{1} f) L

#print axioms rightTensorMap
#print axioms rightTensorMap_element
#print axioms tensorRetractionCochain
#print axioms tensorSectionCochain
#print axioms tensorRetractionCochain_element
#print axioms tensorSectionCochain_element
#print axioms tensor_inclusion_retraction
#print axioms tensor_section_projection
#print axioms element_add_left
#print axioms tensor_decomposition
#print axioms tensorShortComplex
#print axioms tensorDegreeSplitting
#print axioms tensorShortComplex_shortExact
#print axioms tensor_acyclic_of_gradedSplit
#print axioms moduleRelativeKFlat_of_gradedSplit

module
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import Mathlib.Data.ZMod.Basic

/-! # U10a7：全次数で分裂するcone付加と商の普遍性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D} (f : M ⟶ N)
example : ModuleGradedSplit A D (moduleConeInr A D f) (moduleConeConnecting A D f) :=
  moduleConeGradedSplit A D f
example : Mono (moduleConeInr A D f) := moduleConeInr_mono A D f
example : Epi (moduleConeConnecting A D f) := moduleConeConnecting_epi A D f
example : IsColimit (CokernelCofork.ofπ (moduleConeConnecting A D f)
    (moduleConeInr_connecting A D f)) := moduleConeInrCokernel A D f
example (x : D) (n : ℤ) :
    ((moduleConeGradedSplit A D f).evaluationShortComplex x n).ShortExact :=
  (moduleConeGradedSplit A D f).evaluationShortExact x n
example (x y : D) (p i j : ℤ) (hij : i + p = j)
    (a : GradedHom A (Opposite.op x) (Opposite.op y) p) :
    (moduleConeGradedSplit A D f).section_ x i ≫
        moduleActionComponent A D (moduleCone A D f) x y p i j hij a =
      moduleActionComponent A D (M⟦(1 : ℤ)⟧) x y p i j hij a ≫
        (moduleConeGradedSplit A D f).section_ y j :=
  (moduleConeGradedSplit A D f).section_naturality x y p i j hij a
example {M N : ModuleCategory ℤ PUnit.{1}} (f : M ⟶ N) :
    ((moduleConeGradedSplit ℤ PUnit.{1} f).evaluationShortComplex PUnit.unit (-2)).ShortExact :=
  (moduleConeGradedSplit ℤ PUnit.{1} f).evaluationShortExact PUnit.unit (-2)
example {M N : ModuleCategory (ZMod 2) PUnit.{1}} (f : M ⟶ N) :
    ((moduleConeGradedSplit (ZMod 2) PUnit.{1} f).evaluationShortComplex PUnit.unit 1).ShortExact :=
  (moduleConeGradedSplit (ZMod 2) PUnit.{1} f).evaluationShortExact PUnit.unit 1
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_snd_v
#print axioms SerrePositivity.DifferentialGraded.coneMapCochain_inl_v
#print axioms SerrePositivity.DifferentialGraded.complexConeGradedSection
#print axioms SerrePositivity.DifferentialGraded.complexConeGradedRetraction
#print axioms SerrePositivity.DifferentialGraded.complexConeGradedProjection
#print axioms SerrePositivity.DifferentialGraded.complexConeGradedProjection_eq_connecting
#print axioms SerrePositivity.DifferentialGraded.complexConeGradedSection_connecting
#print axioms SerrePositivity.DifferentialGraded.complexConeGradedRetraction_inr
#print axioms SerrePositivity.DifferentialGraded.complexConeGradedSection_retraction
#print axioms SerrePositivity.DifferentialGraded.complexConeGraded_decomposition
#print axioms SerrePositivity.DifferentialGraded.complexConeGradedSection_naturality
#print axioms SerrePositivity.DifferentialGraded.moduleActionComponent
#print axioms SerrePositivity.DifferentialGraded.ModuleGradedSplit
#print axioms SerrePositivity.DifferentialGraded.ModuleGradedSplit.degreewiseMono
#print axioms SerrePositivity.DifferentialGraded.ModuleGradedSplit.degreewiseEpi
#print axioms SerrePositivity.DifferentialGraded.ModuleGradedSplit.mono
#print axioms SerrePositivity.DifferentialGraded.ModuleGradedSplit.epi
#print axioms SerrePositivity.DifferentialGraded.ModuleGradedSplit.evaluationShortComplex
#print axioms SerrePositivity.DifferentialGraded.ModuleGradedSplit.evaluationShortExact
#print axioms SerrePositivity.DifferentialGraded.ModuleGradedSplit.evaluationCokernel
#print axioms SerrePositivity.DifferentialGraded.moduleGradedSplitDescFamily
#print axioms SerrePositivity.DifferentialGraded.moduleGradedSplitDescFamily_fac
#print axioms SerrePositivity.DifferentialGraded.moduleGradedSplitDescFamily_naturality
#print axioms SerrePositivity.DifferentialGraded.moduleGradedSplitDesc
#print axioms SerrePositivity.DifferentialGraded.moduleGradedSplitDesc_fac
#print axioms SerrePositivity.DifferentialGraded.moduleGradedSplitCokernel
#print axioms SerrePositivity.DifferentialGraded.moduleConeInr_connecting
#print axioms SerrePositivity.DifferentialGraded.moduleConeGradedSplit
#print axioms SerrePositivity.DifferentialGraded.moduleConeInr_mono
#print axioms SerrePositivity.DifferentialGraded.moduleConeConnecting_epi
#print axioms SerrePositivity.DifferentialGraded.moduleConeInrCokernel

module
public import SerrePositivity.DifferentialGraded.Module.GradedCoproduct

/-! # U10a10：u-small余積上の全次数分裂 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {J : Type w} [Small.{u} J] {M N P : J → ModuleCategory A D}
variable (f : ∀ t, M t ⟶ N t) (g : ∀ t, N t ⟶ P t)
variable (s : ∀ t, ModuleGradedSplit A D (f t) (g t))
example : ModuleGradedSplit A D (Limits.Sigma.map f) (Limits.Sigma.map g) :=
  moduleCoproductGradedSplit A D f g s
example : Mono (Limits.Sigma.map f) := (moduleCoproductGradedSplit A D f g s).mono
example : Epi (Limits.Sigma.map g) := (moduleCoproductGradedSplit A D f g s).epi
example : IsColimit (CokernelCofork.ofπ (Limits.Sigma.map g)
    (moduleCoproductGradedSplit A D f g s).inclusion_projection) :=
  moduleGradedSplitCokernel A D (moduleCoproductGradedSplit A D f g s)
example (x : D) (n : ℤ) :
    ((moduleCoproductGradedSplit A D f g s).evaluationShortComplex x n).ShortExact :=
  (moduleCoproductGradedSplit A D f g s).evaluationShortExact x n
example (M : ℕ → ModuleCategory A D) (x : D) (n : ℤ) :
    IsColimit (Cofan.mk ((moduleDegreeEvaluation A D x n).obj (∐ M))
      (fun j => (moduleDegreeEvaluation A D x n).map (Sigma.ι M j))) :=
  moduleCoproductDegreeIsColimit A D M x n
example (M : Empty → ModuleCategory A D) (x : D) (n : ℤ) :
    IsColimit (Cofan.mk ((moduleDegreeEvaluation A D x n).obj (∐ M))
      (fun j => (moduleDegreeEvaluation A D x n).map (Sigma.ι M j))) :=
  moduleCoproductDegreeIsColimit A D M x n
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.moduleDegreeEvaluation
#print axioms SerrePositivity.DifferentialGraded.moduleCoproductDegreeIsColimit
#print axioms SerrePositivity.DifferentialGraded.moduleCoproductDegree_hom_ext
#print axioms SerrePositivity.DifferentialGraded.moduleCoproductGradedComponent
#print axioms SerrePositivity.DifferentialGraded.moduleCoproductGradedComponent_ι
#print axioms SerrePositivity.DifferentialGraded.moduleCoproductGradedComponent_comp
#print axioms SerrePositivity.DifferentialGraded.moduleCoproductGradedComponent_id
#print axioms SerrePositivity.DifferentialGraded.moduleCoproductGradedComponent_zero
#print axioms SerrePositivity.DifferentialGraded.moduleCoproductGradedComponent_add
#print axioms SerrePositivity.DifferentialGraded.moduleCoproductGradedComponent_ofMap
#print axioms SerrePositivity.DifferentialGraded.moduleMorphism_actionComponent
#print axioms SerrePositivity.DifferentialGraded.moduleCoproductGradedComponent_naturality
#print axioms SerrePositivity.DifferentialGraded.moduleCoproductGradedSplit

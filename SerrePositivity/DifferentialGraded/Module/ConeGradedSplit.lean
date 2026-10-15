module
public import SerrePositivity.DifferentialGraded.Module.GradedSplit
public import SerrePositivity.DifferentialGraded.Module.GradedSplitCokernel
public import SerrePositivity.DifferentialGraded.Module.ConeMaps
public import SerrePositivity.DifferentialGraded.Complexes.ConeGradedSplit

/-! # cone付加の全次数作用に関する分裂 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleConeInr_connecting {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeInr A D f ≫ moduleConeConnecting A D f = 0 := by
  apply moduleMorphism_ext
  intro x
  rw [CategoryTheory.Functor.map_comp, moduleConeInr_eval, moduleConeConnecting_eval,
    CategoryTheory.Functor.map_zero]
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    complexConeGradedProjection_eq_connecting, complexConeGradedProjection,
    Preadditive.comp_neg, mappingCone.inr_f_fst_v, neg_zero]

/-- cone拡大 N→cone(f)→M[1] は微分を忘れた全次数加群で分裂する。 -/
def moduleConeGradedSplit {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleGradedSplit A D (moduleConeInr A D f) (moduleConeConnecting A D f) where
  retraction x n := complexConeGradedRetraction ((moduleEvaluation A D x).map f) n
  section_ x n := complexConeGradedSection ((moduleEvaluation A D x).map f) n
  inclusion_retraction x n := by
    rw [moduleConeInr_eval]
    exact complexConeGradedRetraction_inr _ n
  section_projection x n := by
    rw [moduleConeConnecting_eval, complexConeGradedProjection_eq_connecting]
    exact complexConeGradedSection_connecting _ n
  section_retraction x n := complexConeGradedSection_retraction _ n
  inclusion_projection := moduleConeInr_connecting A D f
  decomposition x n := by
    rw [moduleConeInr_eval, moduleConeConnecting_eval, complexConeGradedProjection_eq_connecting]
    exact complexConeGraded_decomposition _ n
  retraction_naturality x y p i j hij a := by
    exact coneMapCochain_snd_v _ _ _ _ i j hij
  section_naturality x y p i j hij a := by
    exact complexConeGradedSection_naturality _ _ _ _ i j hij

lemma moduleConeInr_mono {M N : ModuleCategory A D} (f : M ⟶ N) :
    Mono (moduleConeInr A D f) := (moduleConeGradedSplit A D f).mono

lemma moduleConeConnecting_epi {M N : ModuleCategory A D} (f : M ⟶ N) :
    Epi (moduleConeConnecting A D f) := (moduleConeGradedSplit A D f).epi

/-- cone付加の商は主dg加群圏でM[1]。 -/
def moduleConeInrCokernel {M N : ModuleCategory A D} (f : M ⟶ N) :
    IsColimit (CokernelCofork.ofπ (moduleConeConnecting A D f) (moduleConeInr_connecting A D f)) :=
  moduleGradedSplitCokernel A D (moduleConeGradedSplit A D f)

end SerrePositivity.DifferentialGraded

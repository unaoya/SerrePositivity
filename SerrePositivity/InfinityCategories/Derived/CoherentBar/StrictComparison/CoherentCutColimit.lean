module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutDiagram
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentStageColimit
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom

/-!
概要：実正規化 bar は実 dg 次元段階の可算余極限。
方針：評価・次数ごとに包含の単射性と有限 support の網羅性を使う。
規約：余極限をホモロジーのみに置き換えない。
使われ方：h-projective 性の可算段階から全体への移行。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarCutModule_exhaustive (x : D) (q : ℤ)
    (z : ((moduleEvaluation R D x).obj
      (ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModuleUnconditional R D G))).X q) :
    ∃ n a, ((moduleEvaluation R D x).map (dgCoherentBarCutModuleInclusion R D G n)).f q a = z := by
  obtain ⟨n, hn⟩ := dgCoherentBarNormalizedDegreeFiltration_exhaustive R D G x q z
  refine ⟨n, ((moduleEvaluation R D x).map (dgCoherentBarCutProjection R D G n)).f q z, ?_⟩
  rw [dgCoherentBarCutModuleInclusion_eval_f]
  simpa only [moduleDegreeEvaluation, Functor.map_comp, HomologicalComplex.comp_f,
    ModuleCat.comp_apply] using!
    dgCoherentBarCutProjector_recover R D G x q n z hn

def dgCoherentBarCutModuleIsColimit : IsColimit (dgCoherentBarCutModuleCocone R D G) := by
  apply moduleIsColimitOfEvaluations
  intro x
  apply HomologicalComplex.isColimitOfEval
  intro q
  letI := preservesSmallestFilteredColimits_of_preservesFilteredColimits
    (forget (ModuleCat.{u} R))
  exact dgBarFilteredModuleUnionIsColimit R _ _
    (fun n => dgCoherentBarCutModuleInclusion_injective R D G n x q)
    (dgCoherentBarCutModule_exhaustive R D G x q)

end SerrePositivity.InfinityCategories

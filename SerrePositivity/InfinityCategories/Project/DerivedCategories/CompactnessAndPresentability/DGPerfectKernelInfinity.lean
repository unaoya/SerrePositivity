module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectKernelResolution
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedPrecomposition
/-!
概要：一般 kernel の実 perfect 入力と同じ半自由出力から Perf の ∞ 関手を構成する。
方針：実入力射影の指定逆と、perfect 出力射影の dg nerve を合成する。
規約：全単体上の実作用。使われ方：一般 Morita 同値の Perf への制限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 同じ実入力切断による perfect 出力の全単体作用。 -/
def dgPerfectKernelInfinity
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R (PerfectDGModule R D)) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (PerfectDGModule R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelModuleDG R D E P)).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelResolutionReplacement R D E P)
/-- 同じ実入力切断による perfect 出力の全単体作用。 -/
def dgPerfectKernelInfinity_resolvedInclusionIso
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgPerfectKernelInfinity R D E P ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (PerfectDGModule R D) E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelModuleDG R D E P)) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelModuleDG R D E P
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R (PerfectDGModule R D) E F
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelResolutionReplacement R D E P
  have hd := congrArg (fun H => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelResolutionReplacement_projective R D E P)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at hd
  have h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R E)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.inv) _
    rw [hd]
    simpa only [Category.assoc, Category.comp_id] using!
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.homInvIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)
  have h := h0.precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R
      (_root_.SerrePositivity.DifferentialGraded.PerfectDGModule R D)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R (PerfectDGModule R D) E F).inv)
  simpa only [dgPerfectKernelInfinity, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_eq_section_replacement,
    Category.assoc, F, G, L] using! h
end SerrePositivity.InfinityCategories.Project.DerivedCategories

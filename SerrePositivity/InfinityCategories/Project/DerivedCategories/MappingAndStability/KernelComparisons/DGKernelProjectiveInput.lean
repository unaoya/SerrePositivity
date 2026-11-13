module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectKernelResolution
/-!
概要：半自由入力と perfect 入力の kernel 作用を、同じ全射影的入力の作用へ比較する。
方針：実 dg 包含の合成等式と全関手的な出力分解の前合成比較を使う。
規約：元の全単体作用を保つ。使われ方：一般 kernel の Perf 包含四角形。
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
/-- 同じ全射影的入力への kernel 作用の比較。 -/
def dgProjectiveKernelModuleDG (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) (RightModule R E) :=
  (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)).comp
    (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D E P)
/-- 同じ全射影的入力への kernel 作用の比較。 -/
lemma dgProjectiveKernelModuleDG_semifree (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective R D).comp (dgProjectiveKernelModuleDG R D E P) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeKernelModuleDG R D E P := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective, dgProjectiveKernelModuleDG,
    _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion, Category.id_comp, Category.comp_id, eqToHom_refl]
/-- 同じ全射影的入力への kernel 作用の比較。 -/
lemma dgProjectiveKernelModuleDG_perfect (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R D).comp (dgProjectiveKernelModuleDG R D E P) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelModuleDG R D E P := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction,
    dgProjectiveKernelModuleDG, _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion,
    Category.id_comp, Category.comp_id, eqToHom_refl]
/-- 同じ全射影的入力への kernel 作用の比較。 -/
def dgKernelDerivedInfinity_projectiveInputIso (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective R D) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) E
          (dgProjectiveKernelModuleDG R D E P)) := by
  have e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective R D) (dgProjectiveKernelModuleDG R D E P)
  rw [dgProjectiveKernelModuleDG_semifree] at e
  exact e
/-- 同じ全射影的入力への kernel 作用の比較。 -/
def dgPerfectKernelResolvedInfinity_projectiveInputIso (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (PerfectDGModule R D) E
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelModuleDG R D E P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R D) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) E
          (dgProjectiveKernelModuleDG R D E P)) := by
  have e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R (PerfectDGModule R D)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R D) (dgProjectiveKernelModuleDG R D E P)
  rw [dgProjectiveKernelModuleDG_perfect] at e
  exact e
end SerrePositivity.InfinityCategories.Project.DerivedCategories

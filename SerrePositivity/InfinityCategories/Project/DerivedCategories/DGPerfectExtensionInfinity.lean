module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectModulesInfinity
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Derived.Functor
/-!
概要：dg 関手に沿う graph tensor を、実 perfect 加群の安定 ∞ 圏へ制限する。
方針：実射影性と、同じ恒等射影分解で計算した主導来 perfect 保存を使う。
規約：分解の像を別の対象と置き換えない。使われ方：β5 の Perf 上の相対 tensor。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- graph tensor は、同じ実射影的 perfect 加群を実射影的 perfect 加群へ送る。 -/
lemma dgModuleExtension_perfectProjective (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) (M : _root_.SerrePositivity.DifferentialGraded.RightModule R D)
    (hM : _root_.SerrePositivity.DifferentialGraded.modulePerfectProjectiveOver R D Set.univ M) :
    _root_.SerrePositivity.DifferentialGraded.modulePerfectProjectiveOver R E Set.univ ((_root_.SerrePositivity.DifferentialGraded.dgModuleExtension R D E F).obj M) := by
  refine ⟨_root_.SerrePositivity.DifferentialGraded.dgModuleExtension_homotopicallyProjective R D E F hM.1, ?_⟩
  let P := _root_.SerrePositivity.DifferentialGraded.moduleIdentityProjectiveResolution R D (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M) hM.1
  exact (_root_.SerrePositivity.DifferentialGraded.modulePerfect R E).prop_of_iso (_root_.SerrePositivity.DifferentialGraded.dgDerivedExtensionResolutionComputation R D E F P)
    (_root_.SerrePositivity.DifferentialGraded.dgDerivedExtension_perfect R D E F hM.2)
/-- graph tensor の同じ全 Hom 鎖写像を、実 perfect 部分圏へ制限した dg 関手。 -/
def dgPerfectModuleExtension (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.PerfectDGModule R D) (_root_.SerrePositivity.DifferentialGraded.PerfectDGModule R E) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction R _ _ (dgModuleExtension R D E F) _ _
    (dgModuleExtension_perfectProjective R D E F)
/-- Perf の安定 ∞ 圏上の実相対 tensor 関手。 -/
def dgPerfectExtensionInfinity (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectModuleExtension R D E F)
/-- Perf 上の実相対 tensor は完全。 -/
theorem dgPerfectExtensionInfinity_isExactFunctor (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgPerfectExtensionInfinity R D E F) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedModuleFunctorNerve_isExactFunctor R D E (dgModuleExtension R D E F) _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectProperty_closed R D) (dgModuleExtension_perfectProjective R D E F)
end SerrePositivity.InfinityCategories.Project.DerivedCategories

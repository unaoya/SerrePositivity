module
public import SerrePositivity.InfinityCategories.Derived.DGPerfectModulesInfinity
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
variable [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- graph tensor は、同じ実射影的 perfect 加群を実射影的 perfect 加群へ送る。 -/
lemma dgModuleExtension_perfectProjective (F : DGFunctor R D E) (M : RightModule R D)
    (hM : modulePerfectProjectiveOver R D Set.univ M) :
    modulePerfectProjectiveOver R E Set.univ ((dgModuleExtension R D E F).obj M) := by
  refine ⟨dgModuleExtension_homotopicallyProjective R D E F hM.1, ?_⟩
  let P := moduleIdentityProjectiveResolution R D (ForgetEnrichment.of (Complex R) M) hM.1
  exact (modulePerfect R E).prop_of_iso (dgDerivedExtensionResolutionComputation R D E F P)
    (dgDerivedExtension_perfect R D E F hM.2)
/-- graph tensor の同じ全 Hom 鎖写像を、実 perfect 部分圏へ制限した dg 関手。 -/
def dgPerfectModuleExtension (F : DGFunctor R D E) :
    DGFunctor R (PerfectDGModule R D) (PerfectDGModule R E) :=
  dgFullFunctorRestriction R _ _ (dgModuleExtension R D E F) _ _
    (dgModuleExtension_perfectProjective R D E F)
/-- Perf の安定 ∞ 圏上の実相対 tensor 関手。 -/
def dgPerfectExtensionInfinity (F : DGFunctor R D E) :
    dgModulePerfectInfinityCategory R D ⟶ dgModulePerfectInfinityCategory R E :=
  dgNerve.map (dgPerfectModuleExtension R D E F)
/-- Perf 上の実相対 tensor は完全。 -/
theorem dgPerfectExtensionInfinity_isExactFunctor (F : DGFunctor R D E) :
    IsExactFunctor (dgPerfectExtensionInfinity R D E F) :=
  dgClosedModuleFunctorNerve_isExactFunctor R D E (dgModuleExtension R D E F) _ _
    (dgModulePerfectProperty_closed R D) (dgModuleExtension_perfectProjective R D E F)
end SerrePositivity.InfinityCategories

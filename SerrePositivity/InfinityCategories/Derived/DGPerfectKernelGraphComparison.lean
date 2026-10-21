module
public import SerrePositivity.InfinityCategories.Derived.DGPerfectKernelMoritaInfinity
public import SerrePositivity.InfinityCategories.Derived.DGPerfectExtensionCompatibility
public import SerrePositivity.InfinityCategories.Derived.DGKernelGraphComparison
/-!
概要：一般 kernel の同じ graph Morita 作用を、既存の Perf graph 作用へ比較する。
方針：元の D 包含四角形を合成し、完全充満包含で全関手同型を回収する。
規約：生の終点の射影性は不要。使われ方：一般 tensor–Hom の ∞ 随伴への準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ全 Hom 関手と実辺による比較。 -/
instance dgGraphKernelClassical_isEquivalence (F : DGFunctor R D E)
    [(dgDerivedExtension R D E F).IsEquivalence] :
    (Morita.kernelDerivedTensorOnBimodule R D E (functorGraph R D E F)).IsEquivalence := by
  rw [Morita.kernelDerivedTensorOnBimodule_graph]
  infer_instance
/-- 同じ全 Hom 関手と実辺による比較。 -/
def dgPerfectKernelInfinity_graphIso (F : DGFunctor R D E)
    [(dgDerivedExtension R D E F).IsEquivalence] :
    FunctorIso (dgPerfectKernelInfinity R D E (functorGraph R D E F))
      (dgPerfectExtensionInfinity R D E F) := by
  have h := dgPerfectKernelInclusionIso R D E (functorGraph R D E F) ≪≫
    (dgKernelDerivedInfinity_graphIso R D E F).precomp (dgPerfectInclusionInfinity R D) ≪≫
    dgPerfectExtensionInclusionIso R D E F
  exact (dgPerfectInclusionInfinity_isFullyFaithful R E).preimageFunctorIso h
end SerrePositivity.InfinityCategories

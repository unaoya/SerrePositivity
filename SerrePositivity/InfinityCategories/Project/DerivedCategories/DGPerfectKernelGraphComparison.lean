module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectKernelMoritaInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectExtensionCompatibility
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelGraphComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
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
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelInfinity R D E (functorGraph R D E F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R D E F) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelInclusionIso R D E (functorGraph R D E F) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_graphIso R D E F).precomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInclusionIso R D E F
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity_isFullyFaithful R E).preimageFunctorIso h
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module

public import SerrePositivity.KST.LocalizingInvariants.DGExtensionCompositionNerveIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectExtensionInfinity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：D の元の実 Perf 延長の合成を、関手 ∞ 圏の実同型で比較する。
方針：元の全加群上の比較を前合成し、充満 dg 部分圏の包含で反映する。
規約：Perf と延長を再構成しない。使われ方：元の局所化不変量の値の塔。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D E T : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
  [DGCategory R T] [Small.{u} T]

/-- 元の実 perfect 加群から全 dg 加群への充満包含。 -/
def dgPerfectUnderlying : DGFunctor R (PerfectDGModule R D) (RightModule R D) :=
  dgFullSubcategoryInclusion R (RightModule R D) (modulePerfectProjectiveOver R D Set.univ)

lemma dgPerfectExtensionInfinity_underlying (F : DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R D E F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectUnderlying R E) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectUnderlying R D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleExtension R D E F) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectModuleExtension R D E F) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectUnderlying R E) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectUnderlying R D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleExtension R D E F)
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction_inclusion R _ _
    (dgModuleExtension R D E F) _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtension_perfectProjective R D E F))

/-- 元の二つの実 Perf 延長の合成は、元の合成関手に沿う実 Perf 延長と同型。 -/
def dgPerfectExtensionCompositionIso (F : DGFunctor R D E) (G : DGFunctor R E T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R D E F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R E T G)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R D T (F.comp G)) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R T)
    (modulePerfectProjectiveOver R T Set.univ)
  apply hi.preimageFunctorIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R D E F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R E T G) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectUnderlying R T))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R D T (F.comp G) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectUnderlying R T))
  rw [Category.assoc, dgPerfectExtensionInfinity_underlying R E T G,
    ← Category.assoc, dgPerfectExtensionInfinity_underlying R D E F,
    dgPerfectExtensionInfinity_underlying R D T (F.comp G)]
  simpa only [Category.assoc] using
    (dgExtensionCompositionInfinityIso R D E T F G).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectUnderlying R D))

end SerrePositivity.KST.LocalizingInvariants

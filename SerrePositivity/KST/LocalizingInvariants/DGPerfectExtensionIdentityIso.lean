module

public import SerrePositivity.KST.LocalizingInvariants.DGExtensionIdentityComparison
public import SerrePositivity.KST.LocalizingInvariants.DGPerfectExtensionCompositionIso

/-!
概要：D の元の恒等 graph 延長を、全加群と実 Perf の nerve 上の恒等関手へ比較する。
方針：元の同型成分を持つ厳密比較を実関手同型へ移し、元の perfect 包含で反映する。
規約：実加群模型と元の tensor を保持。使われ方：元の不変量値の恒等則。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 元の恒等延長の実ホモトピーから得る、全加群 nerve の恒等比較。 -/
def dgExtensionIdentityInfinityIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleExtension R D D (DGFunctor.id D))) (𝟙 _) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorIsoOfStrictNatTrans R D (dgExtensionIdentityStrict R D)
    (fun M => (dgExtensionIdentityIso R D).hom.app (ForgetEnrichment.of (Complex R) M))
    (dgExtensionIdentityStrict_app_eq R D) (fun _ => inferInstance)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id] at h
  exact h

/-- D の元の実 Perf 恒等延長と恒等 ∞ 関手の同型。 -/
def dgPerfectExtensionIdentityIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R D D (DGFunctor.id D)) (𝟙 _) := by
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSubcategoryInclusionNerve_isFullyFaithful R (RightModule R D)
    (modulePerfectProjectiveOver R D Set.univ)
  apply hi.preimageFunctorIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R D D (DGFunctor.id D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectUnderlying R D))
    (𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectUnderlying R D))
  rw [dgPerfectExtensionInfinity_underlying R D D (DGFunctor.id D), Category.id_comp]
  simpa only [Category.comp_id] using
    (dgExtensionIdentityInfinityIso R D).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectUnderlying R D))

end SerrePositivity.KST.LocalizingInvariants

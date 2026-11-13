module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.Equivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulIso

/-!
概要：perfect 比較の同じ包含を、β5 の元の全関手へ照合する。
方針：実出力分解の augmentation 同型と半自由・射影的比較の余単位を使う。
規約：対象別同型で代用しない。使われ方：DGKappaPerfectInput.inclusion の実構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 逆向き比較も、同じ実導来模型への包含を全関手として保つ。 -/
def dgKappaPerfectReverse_inclusionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectReverse R D I ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I) ≫
        dgKappaConeDerivedComparison R D I) := by
  let C := _root_.SerrePositivity.DifferentialGraded.DGFullSubcategory (DGKappaCone R D I)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))
  let H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :=
    (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (DGKappaCone R D I)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))).comp
        (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) I.objects)
  let F := H.comp (dgConeModuleForget R D)
  let J := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
  let S := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)
  have hF : ∀ x, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D (F.obj x) :=
    fun x => I.projective x.val.val x.val.property
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso R C D F hF
  have hd : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectToPerf R D I).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R D)).comp J = F := by
    apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
    intro X Y
    simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectToPerf, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction, J, dgFullSubcategoryInclusion,
      Category.id_comp, Category.comp_id, eqToHom_refl]
  have h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectReverse R D I ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map S)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
    have h := (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.invHomIso.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J)).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R D))).precomp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectReverse R D I)
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectReverse, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity, S, J,
      Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.comp_id, hd] using! h
  have h₃ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModulesInclusion_isFullyFaithful R D).preimageFunctorIso
    (h₂ ≪≫ h₁.symm)
  have h₄ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R C (ModuleCategory R D) D H
    (dgConeModuleForget R D)
  exact h₃ ≪≫ (by
    simpa only [F, H, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableClosureInclusion, dgKappaConeDerivedComparison,
      dgConeModuleDerived, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] using! h₄)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect

module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedEvaluationQuasiEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：同じ厳密評価の実導来包含を、P が指定した元の全包含へ比較する。
方針：実出力分解と射影的包含を生の加群 nerve で比較し、完全充満包含から全関手同型を戻す。
規約：明示 I・P に条件付き。元の核包含・増大・P の全二胞体を保持する。
使われ方：K-7 c5 の実評価と元の P の全関手照合。対象別同型で代用しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v))
  [DGCategory R D] [Small.{u} D] {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (P : DGKappaPerfectInput R D I)

/-- 同じ元の実小核包含・平坦増大を通る、元の実導来模型への全関手。 -/
def dgKappaResolvedKernelDerived :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (dgKappaResolvedKernelKInput R D I) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedKernelInputMap R D I).down ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)) ≫
      dgKappaConeDerivedComparison R D I

/-- I・P に条件付きで、同じ厳密評価の包含は、元の同じ実出力分解と全関手で同型。 -/
def dgKappaResolvedPerfectEvaluation_resolvedIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedPerfectEvaluation R D I P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (dgKappaResolvedKernelKInput R D I) D
        (dgKappaResolvedEvaluationBimodule R D I)) := by
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso R (dgKappaResolvedKernelKInput R D I) D
    (dgKappaResolvedEvaluationBimodule R D I)
    (dgKappaResolvedEvaluationBimodule_column_projective R D I)
  have hp0 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R D)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R D Set.univ)) := by
    let e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose
    let J := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
    have h := (e.invHomIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map J)).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R D))
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity, Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
      Category.comp_id] using! h
  have hp := hp0.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedPerfectEvaluation R D I P))
  have hE : (dgKappaResolvedPerfectEvaluation R D I P).comp
      (perfectDGModuleInclusion R D Set.univ) = dgKappaResolvedEvaluationBimodule R D I := by
    exact DGFunctor.restrict_comp_inclusion _ _ _ _
  have hN := congrArg (fun F => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) hE
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at hN
  rw [hN] at hp
  have h := hr ≪≫ hp.symm
  exact ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModulesInclusion_isFullyFaithful R D).preimageFunctorIso
    (by simpa only [Category.assoc] using! h)).symm

/-- 同じ実出力分解は、元の実核包含・増大による元の全導来比較を保持する。 -/
def dgKappaResolvedEvaluation_resolvedKernelIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (dgKappaResolvedKernelKInput R D I) D
      (dgKappaResolvedEvaluationBimodule R D I)) (dgKappaResolvedKernelDerived R D I) := by
  let H := ((dgKappaResolvedKernelInputMap R D I).down.comp
    (DGCategoryCellResolution.augmentation R (DGKappaCone R D I))).comp
      (dgFullSubcategoryInclusion R (ModuleCategory R D) I.objects)
  have hE : H.comp (dgConeModuleForget R D) = dgKappaResolvedEvaluationBimodule R D I := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [EnrichedFunctor.comp_map, Category.assoc, eqToHom_refl, Category.comp_id]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R (dgKappaResolvedKernelKInput R D I)
    (ModuleCategory R D) D H (dgConeModuleForget R D)
  rw [hE] at h
  simpa only [H, dgKappaResolvedKernelDerived, dgKappaConeDerivedComparison,
    dgConeModuleDerived, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] using! h

/-- I・P に条件付きで、同じ実評価の導来包含は元の核包含と平坦増大を通る全比較そのもの。 -/
def dgKappaResolvedPerfectEvaluation_inclusionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedPerfectEvaluation R D I P) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D) (dgKappaResolvedKernelDerived R D I) :=
  dgKappaResolvedPerfectEvaluation_resolvedIso R D I P ≪≫
    dgKappaResolvedEvaluation_resolvedKernelIso R D I

/-- I・P に条件付きで、元の P の全関手と同じ実評価の合成は、元の Perf の恒等に同型。 -/
def dgKappaPerfectResolvedComparison_evaluationIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKappaPerfectResolvedComparison R D I P ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaResolvedPerfectEvaluation R D I P))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D)) := by
  have e₁ := (dgKappaResolvedPerfectEvaluation_inclusionIso R D I P).precomp
    (dgKappaPerfectResolvedComparison R D I P)
  have e₂ := dgKappaPerfectResolvedComparison_inclusion R D I P
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity_isFullyFaithful R D).preimageFunctorIso
  simpa only [dgKappaResolvedKernelDerived, Category.assoc, Category.id_comp] using!
    e₁ ≪≫ e₂

end SerrePositivity.KST.NonConnective

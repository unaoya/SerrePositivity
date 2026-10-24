module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedEvaluationQuasiEquivalence
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition

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
    dgNerve R (dgKappaResolvedKernelKInput R D I) ⟶ dgModuleDerivedInfinityCategory R D :=
  dgNerve.map (dgKappaResolvedKernelInputMap R D I).down ≫
    dgNerve.map (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)) ≫
      dgKappaConeDerivedComparison R D I

/-- I・P に条件付きで、同じ厳密評価の包含は、元の同じ実出力分解と全関手で同型。 -/
def dgKappaResolvedPerfectEvaluation_resolvedIso :
    FunctorIso (dgNerve.map (dgKappaResolvedPerfectEvaluation R D I P) ≫
      dgPerfectInclusionInfinity R D)
      (dgModuleResolvedInfinity R (dgKappaResolvedKernelKInput R D I) D
        (dgKappaResolvedEvaluationBimodule R D I)) := by
  have hr := dgModuleResolvedInfinity_inclusionIso R (dgKappaResolvedKernelKInput R D I) D
    (dgKappaResolvedEvaluationBimodule R D I)
    (dgKappaResolvedEvaluationBimodule_column_projective R D I)
  have hp0 : FunctorIso (dgPerfectInclusionInfinity R D ≫ dgNerve.map
      (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)))
      (dgNerve.map (perfectDGModuleInclusion R D Set.univ)) := by
    let e := (dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose
    let J := dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)
    have h := (e.invHomIso.postcomp (dgNerve.map J)).precomp
      (dgNerve.map (dgPerfectToProjective R D))
    simpa only [dgPerfectInclusionInfinity, Category.assoc, ← dgNerve.map_comp,
      Category.comp_id] using! h
  have hp := hp0.precomp (dgNerve.map (dgKappaResolvedPerfectEvaluation R D I P))
  have hE : (dgKappaResolvedPerfectEvaluation R D I P).comp
      (perfectDGModuleInclusion R D Set.univ) = dgKappaResolvedEvaluationBimodule R D I := by
    exact DGFunctor.restrict_comp_inclusion _ _ _ _
  have hN := congrArg (fun F => dgNerve.map F) hE
  rw [dgNerve.map_comp] at hN
  rw [hN] at hp
  have h := hr ≪≫ hp.symm
  exact ((dgSemifreeModulesInclusion_isFullyFaithful R D).preimageFunctorIso
    (by simpa only [Category.assoc] using! h)).symm

/-- 同じ実出力分解は、元の実核包含・増大による元の全導来比較を保持する。 -/
def dgKappaResolvedEvaluation_resolvedKernelIso :
    FunctorIso (dgModuleResolvedInfinity R (dgKappaResolvedKernelKInput R D I) D
      (dgKappaResolvedEvaluationBimodule R D I)) (dgKappaResolvedKernelDerived R D I) := by
  let H := ((dgKappaResolvedKernelInputMap R D I).down.comp
    (DGCategoryCellResolution.augmentation R (DGKappaCone R D I))).comp
      (dgFullSubcategoryInclusion R (ModuleCategory R D) I.objects)
  have hE : H.comp (dgConeModuleForget R D) = dgKappaResolvedEvaluationBimodule R D I := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [EnrichedFunctor.comp_map, Category.assoc, eqToHom_refl, Category.comp_id]
  have h := dgModuleResolvedInfinity_precompIso R (dgKappaResolvedKernelKInput R D I)
    (ModuleCategory R D) D H (dgConeModuleForget R D)
  rw [hE] at h
  simpa only [H, dgKappaResolvedKernelDerived, dgKappaConeDerivedComparison,
    dgConeModuleDerived, dgNerve.map_comp, Category.assoc] using! h

/-- I・P に条件付きで、同じ実評価の導来包含は元の核包含と平坦増大を通る全比較そのもの。 -/
def dgKappaResolvedPerfectEvaluation_inclusionIso :
    FunctorIso (dgNerve.map (dgKappaResolvedPerfectEvaluation R D I P) ≫
      dgPerfectInclusionInfinity R D) (dgKappaResolvedKernelDerived R D I) :=
  dgKappaResolvedPerfectEvaluation_resolvedIso R D I P ≪≫
    dgKappaResolvedEvaluation_resolvedKernelIso R D I

/-- I・P に条件付きで、元の P の全関手と同じ実評価の合成は、元の Perf の恒等に同型。 -/
def dgKappaPerfectResolvedComparison_evaluationIso :
    FunctorIso (dgKappaPerfectResolvedComparison R D I P ≫
      dgNerve.map (dgKappaResolvedPerfectEvaluation R D I P))
      (𝟙 (dgModulePerfectInfinityCategory R D)) := by
  have e₁ := (dgKappaResolvedPerfectEvaluation_inclusionIso R D I P).precomp
    (dgKappaPerfectResolvedComparison R D I P)
  have e₂ := dgKappaPerfectResolvedComparison_inclusion R D I P
  apply (dgPerfectInclusionInfinity_isFullyFaithful R D).preimageFunctorIso
  simpa only [dgKappaResolvedKernelDerived, Category.assoc, Category.id_comp] using!
    e₁ ≪≫ e₂

end SerrePositivity.KST.NonConnective

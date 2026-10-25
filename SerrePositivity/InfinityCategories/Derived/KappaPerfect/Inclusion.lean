module
public import SerrePositivity.InfinityCategories.Derived.KappaPerfect.Equivalence
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulIso

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 逆向き比較も、同じ実導来模型への包含を全関手として保つ。 -/
def dgKappaPerfectReverse_inclusionIso :
    FunctorIso (dgKappaPerfectReverse R D I ≫ dgPerfectInclusionInfinity R D)
      (dgStableClosureInclusion R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I) ≫
        dgKappaConeDerivedComparison R D I) := by
  let C := DGFullSubcategory (DGKappaCone R D I)
    (dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))
  let H : DGFunctor R C (ModuleCategory R D) :=
    (dgFullSubcategoryInclusion R (DGKappaCone R D I)
      (dgStableClosureProperty R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I))).comp
        (dgFullSubcategoryInclusion R (ModuleCategory R D) I.objects)
  let F := H.comp (dgConeModuleForget R D)
  let J := dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)
  let S := dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)
  have hF : ∀ x, dgModuleProjectiveProperty R D (F.obj x) :=
    fun x => I.projective x.val.val x.val.property
  have h₁ := dgModuleResolvedInfinity_inclusionIso R C D F hF
  have hd : ((dgKappaPerfectToPerf R D I).comp (dgPerfectToProjective R D)).comp J = F := by
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro X Y
    simp only [EnrichedFunctor.comp_map, dgKappaPerfectToPerf, dgPerfectToProjective,
      dgFullFunctorRestriction, J, dgFullSubcategoryInclusion,
      Category.id_comp, Category.comp_id, eqToHom_refl]
  have h₂ : FunctorIso
      ((dgKappaPerfectReverse R D I ≫ dgPerfectInclusionInfinity R D) ≫ dgNerve.map S)
      (dgNerve.map F) := by
    have h := (((dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.invHomIso.postcomp
      (dgNerve.map J)).precomp (dgNerve.map (dgPerfectToProjective R D))).precomp
        (dgKappaPerfectReverse R D I)
    simpa only [dgKappaPerfectReverse, dgPerfectInclusionInfinity, S, J,
      Category.assoc, ← dgNerve.map_comp, Category.comp_id, hd] using! h
  have h₃ := (dgSemifreeModulesInclusion_isFullyFaithful R D).preimageFunctorIso
    (h₂ ≪≫ h₁.symm)
  have h₄ := dgModuleResolvedInfinity_precompIso R C (ModuleCategory R D) D H
    (dgConeModuleForget R D)
  exact h₃ ≪≫ (by
    simpa only [F, H, dgStableClosureInclusion, dgKappaConeDerivedComparison,
      dgConeModuleDerived, dgNerve.map_comp, Category.assoc] using! h₄)

end SerrePositivity.InfinityCategories

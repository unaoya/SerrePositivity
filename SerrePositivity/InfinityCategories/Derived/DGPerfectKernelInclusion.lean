module
public import SerrePositivity.InfinityCategories.Derived.DGPerfectKernelInfinity
public import SerrePositivity.InfinityCategories.Derived.DGKernelProjectiveInput
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulIso
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus
/-!
概要：一般 kernel の Perf 作用と元の D 作用の包含四角形を全関手同型で比較する。
方針：元の全単体作用・実入力切断と perfect 性の保存反映を使う。
規約：高次 Hom の検査を省かない。使われ方：一般 Morita の Perf の結論。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の一般 kernel の実 perfect 出力による比較。 -/
def dgPerfectKernelInclusionIso
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    FunctorIso (dgPerfectKernelInfinity R D E P ≫ dgPerfectInclusionInfinity R E)
      (dgPerfectInclusionInfinity R D ≫ dgKernelDerivedInfinity R D E P) := by
  let L := dgModuleResolvedInfinity R (ProjectiveDGModules R D) E
    (dgProjectiveKernelModuleDG R D E P)
  have e1 := (dgKernelDerivedInfinity_projectiveInputIso R D E P).precomp
    (dgPerfectInclusionInfinity R D)
  have e2 := ((dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.invHomIso.precomp
    (dgNerve.map (dgPerfectToProjective R D))).postcomp L
  have e3 : FunctorIso (dgPerfectInclusionInfinity R D ≫ dgKernelDerivedInfinity R D E P)
      (dgNerve.map (dgPerfectToProjective R D) ≫ L) := by
    exact e1 ≪≫ (by simpa only [dgPerfectInclusionInfinity, Category.assoc,
      Category.comp_id, L] using! e2)
  exact dgPerfectKernelInfinity_resolvedInclusionIso R D E P ≪≫
    dgPerfectKernelResolvedInfinity_projectiveInputIso R D E P ≪≫ e3.symm
/-- 元の一般 kernel の実 perfect 出力による比較。 -/
lemma dgPerfectKernelInfinity_isFullyFaithful
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    IsFullyFaithful (dgPerfectKernelInfinity R D E P) := by
  have h := (dgPerfectInclusionInfinity_isFullyFaithful R D).comp
    (dgKernelDerivedInfinity_isQCatEquivalence_of_classical R D E P).isFullyFaithful
  have h' := (dgPerfectKernelInclusionIso R D E P).isFullyFaithful_iff.mpr h
  exact (dgPerfectInclusionInfinity_isFullyFaithful R E).cancel_right h'
end SerrePositivity.InfinityCategories

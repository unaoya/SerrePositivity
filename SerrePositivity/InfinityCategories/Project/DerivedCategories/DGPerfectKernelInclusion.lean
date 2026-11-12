module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectKernelInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelProjectiveInput
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の一般 kernel の実 perfect 出力による比較。 -/
def dgPerfectKernelInclusionIso
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelInfinity R D E P ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R E)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P) := by
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) E
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveKernelModuleDG R D E P)
  have e1 := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_projectiveInputIso R D E P).precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D)
  have e2 := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.invHomIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R D))).postcomp L
  have e3 : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity R D ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectToProjective R D) ≫ L) := by
    exact e1 ≪≫ (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity, Category.assoc,
      Category.comp_id, L] using! e2)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelInfinity_resolvedInclusionIso R D E P ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelResolvedInfinity_projectiveInputIso R D E P ≪≫ e3.symm
/-- 元の一般 kernel の実 perfect 出力による比較。 -/
lemma dgPerfectKernelInfinity_isFullyFaithful
    (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) [(_root_.SerrePositivity.DifferentialGraded.Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectKernelInfinity R D E P) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity_isFullyFaithful R D).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_isQCatEquivalence_of_classical R D E P).isFullyFaithful
  have h' := (dgPerfectKernelInclusionIso R D E P).isFullyFaithful_iff.mpr h
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectInclusionInfinity_isFullyFaithful R E).cancel_right h'
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ClosedSectionDescent
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.ProjectorComponents
/-!
概要：退化因子を消す安定自己写像から、同じ正規化実 bar への変形 retract を得る。
方針：既存の全 Hom の因子化を評価成分へ移し、次数付き切断の降下を適用する。
規約：退化因子の消去は明示した命題として保持し、無条件の結論と取り違えない。
使われ方：退化係数の検証後に修正包含・厳密分裂・全作用鎖ホモトピーをまとめて公開する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory Limits DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

abbrev DGCoherentBarNormalizationKillsDegenerate : Prop :=
  ∀ s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegenerateIndex I,
    (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)).f 0
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationProjectorGraded R D F) = 0

variable (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)
  (hdeg : DGCoherentBarNormalizationKillsDegenerate R D F)

include hdeg in
lemma dgCoherentBarNormalizationEndomorphism_factor_evaluation (x : D) (n : ℤ) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC)).f n ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedGradedSection R D F hMC x n ≫
      ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphism R D F hMC)).f n =
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphism R D F hMC)).f n := by
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedModuleProjection_evaluation_f,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizationEndomorphism_evaluation_f]
  have hf := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_factor_normalized R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F) 0
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationProjectorGraded R D F) hdeg
  have hv := congrArg (fun z => ((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) x).f 0 z).v
      n n (add_zero n)) hf
  simp only [_root_.SerrePositivity.DifferentialGraded.moduleHomWhiskerRight_apply_π, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v] at hv
  exact hv

def dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) ⟶
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarObject R D F hMC :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgBarRetract_correctedSection R D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedGradedSection R D F hMC)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedGradedSection_naturality R D F hMC)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizedGradedSection_projection R D F hMC)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphism R D F hMC)
    (dgCoherentBarNormalizationEndomorphism_factor_evaluation R D F hMC hdeg)

lemma dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish_projection :
    dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish R D F hMC hdeg ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC = 𝟙 _ :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgBarRetract_correctedSection_projection R D _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarNormalizationEndomorphism_projection R D F hMC)

lemma dgCoherentBarNormalizedModuleProjection_inclusionOfDegenerateVanish :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC ≫
      dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish R D F hMC hdeg =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphism R D F hMC :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgBarRetract_projection_correctedSection R D _ _ _ _ _ _

def dgCoherentBarNormalizedModuleRetractHomotopyOfDegenerateVanish :
    _root_.SerrePositivity.DifferentialGraded.ModuleHomotopy R D
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleProjection R D F hMC ≫
        dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish R D F hMC hdeg) (𝟙 _) := by
  rw [dgCoherentBarNormalizedModuleProjection_inclusionOfDegenerateVanish]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizationEndomorphismHomotopy R D F hMC

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract

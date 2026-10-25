module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.ClosedSectionDescent
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.ProjectorComponents
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

abbrev DGCoherentBarNormalizationKillsDegenerate : Prop :=
  ∀ s : dgCoherentBarDegenerateIndex I,
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s.val)
      (dgCoherentBarGraded R D F)).f 0
      (dgCoherentBarNormalizationProjectorGraded R D F) = 0

variable (hMC : dgCoherentBarMaurerCartan R D F)
  (hdeg : DGCoherentBarNormalizationKillsDegenerate R D F)

include hdeg in
lemma dgCoherentBarNormalizationEndomorphism_factor_evaluation (x : D) (n : ℤ) :
    ((moduleEvaluation R D x).map
        (dgCoherentBarNormalizedModuleProjection R D F hMC)).f n ≫
      dgCoherentBarNormalizedGradedSection R D F hMC x n ≫
      ((moduleEvaluation R D x).map
        (dgCoherentBarNormalizationEndomorphism R D F hMC)).f n =
    ((moduleEvaluation R D x).map
      (dgCoherentBarNormalizationEndomorphism R D F hMC)).f n := by
  rw [dgCoherentBarNormalizedModuleProjection_evaluation_f,
    dgCoherentBarNormalizationEndomorphism_evaluation_f]
  have hf := dgCoherentBarHom_factor_normalized R D F (dgCoherentBarGraded R D F) 0
    (dgCoherentBarNormalizationProjectorGraded R D F) hdeg
  have hv := congrArg (fun z => ((moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) x).f 0 z).v
      n n (add_zero n)) hf
  simp only [moduleHomWhiskerRight_apply_π, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v] at hv
  exact hv

def dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish :
    ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModule R D F hMC) ⟶
      dgCoherentBarObject R D F hMC :=
  dgBarRetract_correctedSection R D
    (dgCoherentBarNormalizedModuleProjection R D F hMC)
    (dgCoherentBarNormalizedGradedSection R D F hMC)
    (dgCoherentBarNormalizedGradedSection_naturality R D F hMC)
    (dgCoherentBarNormalizedGradedSection_projection R D F hMC)
    (dgCoherentBarNormalizationEndomorphism R D F hMC)
    (dgCoherentBarNormalizationEndomorphism_factor_evaluation R D F hMC hdeg)

lemma dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish_projection :
    dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish R D F hMC hdeg ≫
      dgCoherentBarNormalizedModuleProjection R D F hMC = 𝟙 _ :=
  dgBarRetract_correctedSection_projection R D _ _ _ _ _ _
    (dgCoherentBarNormalizationEndomorphism_projection R D F hMC)

lemma dgCoherentBarNormalizedModuleProjection_inclusionOfDegenerateVanish :
    dgCoherentBarNormalizedModuleProjection R D F hMC ≫
      dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish R D F hMC hdeg =
      dgCoherentBarNormalizationEndomorphism R D F hMC :=
  dgBarRetract_projection_correctedSection R D _ _ _ _ _ _

def dgCoherentBarNormalizedModuleRetractHomotopyOfDegenerateVanish :
    ModuleHomotopy R D
      (dgCoherentBarNormalizedModuleProjection R D F hMC ≫
        dgCoherentBarNormalizedModuleInclusionOfDegenerateVanish R D F hMC hdeg) (𝟙 _) := by
  rw [dgCoherentBarNormalizedModuleProjection_inclusionOfDegenerateVanish]
  exact dgCoherentBarNormalizationEndomorphismHomotopy R D F hMC

end SerrePositivity.InfinityCategories

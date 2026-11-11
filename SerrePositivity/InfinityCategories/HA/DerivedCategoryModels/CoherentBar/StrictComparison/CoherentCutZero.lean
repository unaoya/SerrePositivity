module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentGradedProjective
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.MaurerCartanZeroIso
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentZeroStage

/-!
概要：零段階では θ が消えるので、h-projective 頂点の零段階も h-projective。
方針：零次元支持上の θ 消滅を制限し、零 MC 変更の同型を使う。
規約：高次 HA 項は全体では保ち、零段階でだけ消滅を使う。
使われ方：実 dg 段階の射影性の帰納の初期値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarCutTheta_zero : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta R D G 0 = 0 := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
  intro x
  apply Cochain.ext
  intro q r hqr
  subst r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutTheta]
  erw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomogeneous_pre_apply R D
    (M := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G 0) (N := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G)
    (P := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G 0) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion R D G 0) 1 _ x q z,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomogeneous_post_apply R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutProjection R D G 0) 1
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta R D G) x q]
  have hz := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration_zero_theta R D G x q _
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutInclusion_mem R D G x q 0 z)
  rw [hz, map_zero]
  simp only [map_zero, Cochain.zero_v, ModuleCat.hom_zero, LinearMap.zero_apply]

def dgCoherentBarCutZeroIso :
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModule R D G 0) ≅
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded R D G 0 := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModule]
  simp only [dgCoherentBarCutTheta_zero]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarMaurerCartanZeroIso R D _

lemma dgCoherentBarCutZero_projective
    (hG : ∀ s : I _⦋0⦌, _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R D
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramVertex G s))) :
    _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective R D
      (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutModule R D G 0)) :=
  _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_of_iso R D (dgCoherentBarCutZeroIso R D G).symm
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarCutGraded_projective R D G hG 0)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentGradedProjective
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.MaurerCartanZeroIso
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStage

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarCutTheta_zero : dgCoherentBarCutTheta R D G 0 = 0 := by
  apply moduleHomElement_ext R D
  intro x
  apply Cochain.ext
  intro q r hqr
  subst r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  dsimp only [dgCoherentBarCutTheta]
  erw [← dgCoherentBarHomogeneous_pre_apply R D
    (M := dgCoherentBarCutGraded R D G 0) (N := dgCoherentBarNormalizedGraded R D G)
    (P := dgCoherentBarCutGraded R D G 0) (dgCoherentBarCutInclusion R D G 0) 1 _ x q z,
    dgCoherentBarHomogeneous_post_apply R D (dgCoherentBarCutProjection R D G 0) 1
      (dgCoherentBarNormalizedTheta R D G) x q]
  have hz := dgCoherentBarNormalizedDegreeFiltration_zero_theta R D G x q _
    (dgCoherentBarCutInclusion_mem R D G x q 0 z)
  rw [hz, map_zero]
  simp only [map_zero, Cochain.zero_v, ModuleCat.hom_zero, LinearMap.zero_apply]

def dgCoherentBarCutZeroIso :
    ForgetEnrichment.of (Complex R) (dgCoherentBarCutModule R D G 0) ≅
      dgCoherentBarCutGraded R D G 0 := by
  dsimp only [dgCoherentBarCutModule]
  simp only [dgCoherentBarCutTheta_zero]
  exact dgBarMaurerCartanZeroIso R D _

lemma dgCoherentBarCutZero_projective
    (hG : ∀ s : I _⦋0⦌, moduleHomotopicallyProjective R D
      (ForgetEnrichment.of (Complex R) (coherentDiagramVertex G s))) :
    moduleHomotopicallyProjective R D
      (ForgetEnrichment.of (Complex R) (dgCoherentBarCutModule R D G 0)) :=
  moduleHomotopicallyProjective_of_iso R D (dgCoherentBarCutZeroIso R D G).symm
    (dgCoherentBarCutGraded_projective R D G hG 0)

end SerrePositivity.InfinityCategories

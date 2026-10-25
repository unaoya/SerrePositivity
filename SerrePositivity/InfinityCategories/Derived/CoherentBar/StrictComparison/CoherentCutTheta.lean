module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutGraded
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentDegreeDifferential
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.MaurerCartanRestriction

/-!
概要：実正規化 θ を単体次元の有限上限を持つ実 dg 直和に制限する。
方針：θ の一段下降と、次数上限に沿う分裂射影の回収式を使う。
規約：全ての高次 HA 項を含む同じ θ を制限する。
使われ方：h-projective な層を持つ実 dg 加群段階の MC 微分。
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
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarCutInclusion_mem (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarCutGraded R D G n)) :
    (moduleDegreeEvaluation R D x q).map (dgCoherentBarCutInclusion R D G n) z ∈
      dgCoherentBarNormalizedDegreeFiltration R D G x q n := by
  classical
  obtain ⟨t, a, ha⟩ := moduleCofan_element_rep R
    (fun s => (moduleDegreeEvaluation R D x q).obj (dgCoherentBarCutFamily R D G n s)) _
    (moduleCoproductDegreeIsColimit R D (dgCoherentBarCutFamily R D G n) x q) z
  rw [← ha, map_sum]
  apply Submodule.sum_mem
  intro s hs
  change (moduleDegreeEvaluation R D x q).map (dgCoherentBarCutInclusion R D G n)
    ((moduleDegreeEvaluation R D x q).map (Sigma.ι (dgCoherentBarCutFamily R D G n) s) (a s)) ∈ _
  erw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp, dgCoherentBarCutInclusion_ι]
  exact dgCoherentBarNormalizedDegreeFiltration_inclusion R D G x q n s.val s.property (a s)

def dgCoherentBarCutTheta (n : ℕ) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarCutGraded R D G n))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarCutGraded R D G n))).X 1 :=
  (eHomWhiskerRight (Complex R) (dgCoherentBarCutInclusion R D G n)
    (dgCoherentBarCutGraded R D G n)).f 1
    ((eHomWhiskerLeft (Complex R) (dgCoherentBarNormalizedGraded R D G)
      (dgCoherentBarCutProjection R D G n)).f 1 (dgCoherentBarNormalizedTheta R D G))

set_option maxHeartbeats 800000 in
-- The same selected Hom end is evaluated through four restriction maps.
lemma dgCoherentBarCutTheta_inclusion (n : ℕ) :
    (eHomWhiskerRight (Complex R) (dgCoherentBarCutInclusion R D G n)
      (dgCoherentBarNormalizedGraded R D G)).f 1 (dgCoherentBarNormalizedTheta R D G) =
    (eHomWhiskerLeft (Complex R) (dgCoherentBarCutGraded R D G n)
      (dgCoherentBarCutInclusion R D G n)).f 1 (dgCoherentBarCutTheta R D G n) := by
  apply moduleHomElement_ext R D
  intro x
  apply Cochain.ext
  intro q r hqr
  subst r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  erw [← dgCoherentBarHomogeneous_pre_apply R D
    (dgCoherentBarCutInclusion R D G n) 1 (dgCoherentBarNormalizedTheta R D G) x q z,
    dgCoherentBarHomogeneous_post_apply R D (dgCoherentBarCutInclusion R D G n)
      1 (dgCoherentBarCutTheta R D G n) x q z]
  dsimp only [dgCoherentBarCutTheta]
  erw [← dgCoherentBarHomogeneous_pre_apply R D
    (M := dgCoherentBarCutGraded R D G n)
    (N := dgCoherentBarNormalizedGraded R D G) (P := dgCoherentBarCutGraded R D G n)
    (dgCoherentBarCutInclusion R D G n) 1
      ((eHomWhiskerLeft (Complex R) (dgCoherentBarNormalizedGraded R D G)
        (dgCoherentBarCutProjection R D G n)).f 1 (dgCoherentBarNormalizedTheta R D G)) x q z,
    dgCoherentBarHomogeneous_post_apply R D (dgCoherentBarCutProjection R D G n) 1
      (dgCoherentBarNormalizedTheta R D G) x q
      ((moduleDegreeEvaluation R D x q).map (dgCoherentBarCutInclusion R D G n) z)]
  have hm := dgCoherentBarCutInclusion_mem R D G x q n z
  have ht := dgCoherentBarNormalizedDegreeFiltration_theta R D G x q n _ hm
  have ht' := dgCoherentBarNormalizedDegreeFiltration_mono R D G x (q + 1) (Nat.sub_le n 1) ht
  have hr := dgCoherentBarCutProjector_recover R D G x (q + 1) n _ ht'
  simpa only [CategoryTheory.Functor.map_comp, ModuleCat.comp_apply,
    HomologicalComplex.comp_f] using! hr.symm

lemma dgCoherentBarCutTheta_maurerCartan (n : ℕ) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (dgCoherentBarCutGraded R D G n))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarCutGraded R D G n))).d 1 2
        (dgCoherentBarCutTheta R D G n) +
      compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarCutGraded R D G n))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarCutGraded R D G n))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarCutGraded R D G n))
        (dgCoherentBarCutTheta R D G n) (dgCoherentBarCutTheta R D G n)
        (show (1 : ℤ) + 1 = 2 from rfl) = 0 :=
  dgBarModuleMaurerCartan_restrict R D (dgCoherentBarCutInclusion R D G n)
    (dgCoherentBarCutProjection R D G n) (dgCoherentBarCutInclusion_projection R D G n)
    _ _ (dgCoherentBarCutTheta_inclusion R D G n)
    (dgCoherentBarNormalizedTheta_maurerCartan R D G (dgCoherentBarMaurerCartan_unconditional R D G))

end SerrePositivity.InfinityCategories

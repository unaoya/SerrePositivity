module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentCutModule
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.MaurerCartanZeroIso
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerDifferential

/-!
概要：実 dg 加群の n 段階から n 次元の内部層への射を構成する。
方針：θ は単体次元を下げるので最高層への射影で消えることを使う。
規約：最高層の商の微分は元の各頂点加群の内部微分である。
使われ方：隣接段階の全次数分裂拡大と射影性の帰納。
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

def dgCoherentBarCutToLayerGraded (n : ℕ) :
    dgCoherentBarCutGraded R D G n ⟶ dgCoherentBarLayerGraded R D G n :=
  dgCoherentBarCutInclusion R D G n ≫ dgCoherentBarLayerProjection R D G n

lemma dgCoherentBarCutToLayerGraded_theta (n : ℕ) :
    (eHomWhiskerLeft (Complex R) (dgCoherentBarCutGraded R D G n)
      (dgCoherentBarCutToLayerGraded R D G n)).f 1 (dgCoherentBarCutTheta R D G n) = 0 := by
  apply moduleHomElement_ext R D
  intro x
  apply Cochain.ext
  intro q r hqr
  subst r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  erw [dgCoherentBarHomogeneous_post_apply R D (dgCoherentBarCutToLayerGraded R D G n)
    1 (dgCoherentBarCutTheta R D G n) x q z]
  have hi := congrArg (fun a => ((moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (dgCoherentBarCutGraded R D G n))
    (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G)) x).f 1 a).v
      q (q + 1) rfl z) (dgCoherentBarCutTheta_inclusion R D G n)
  erw [← dgCoherentBarHomogeneous_pre_apply R D (dgCoherentBarCutInclusion R D G n)
    1 (dgCoherentBarNormalizedTheta R D G) x q z,
    dgCoherentBarHomogeneous_post_apply R D (dgCoherentBarCutInclusion R D G n)
      1 (dgCoherentBarCutTheta R D G n) x q z] at hi
  have hz := dgCoherentBarLayerProjection_theta_zero R D G x q n _
    (dgCoherentBarCutInclusion_mem R D G x q n z)
  dsimp only [dgCoherentBarCutToLayerGraded]
  rw [CategoryTheory.Functor.map_comp, ModuleCat.comp_apply]
  change (moduleDegreeEvaluation R D x (q + 1)).map (dgCoherentBarLayerProjection R D G n)
    ((moduleDegreeEvaluation R D x (q + 1)).map (dgCoherentBarCutInclusion R D G n)
      ((((moduleHomπ R D _ _ x).f 1 (dgCoherentBarCutTheta R D G n)).v q (q + 1) rfl) z)) = _
  rw [← hi, hz]
  simp only [map_zero, Cochain.zero_v, ModuleCat.hom_zero, LinearMap.zero_apply]

def dgCoherentBarCutToLayer (n : ℕ) :
    ForgetEnrichment.of (Complex R) (dgCoherentBarCutModule R D G n) ⟶
      dgCoherentBarLayerGraded R D G n :=
  dgBarMaurerCartanModuleMap R D (dgCoherentBarCutTheta R D G n) 0
    (dgCoherentBarCutTheta_maurerCartan R D G n)
    (dgBarModuleZero_maurerCartan R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G n)))
    (dgCoherentBarCutToLayerGraded R D G n)
    (by rw [map_zero, dgCoherentBarCutToLayerGraded_theta]) ≫
    (dgBarMaurerCartanZeroIso R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G n))).hom

@[simp]
lemma dgCoherentBarCutToLayer_eval_f (n : ℕ) (x : D) (q : ℤ) :
    ((moduleEvaluation R D x).map (dgCoherentBarCutToLayer R D G n)).f q =
      ((moduleEvaluation R D x).map (dgCoherentBarCutToLayerGraded R D G n)).f q := by
  simp only [dgCoherentBarCutToLayer, CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
    dgBarMaurerCartanModuleMap_eval_f, dgBarMaurerCartanZeroIso_hom_eval_f, Category.comp_id]

end SerrePositivity.InfinityCategories

module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerAnnihilation
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentZeroStage
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentStages

/-!
概要：同じ単体次元層への射影は、その段階上で実微分を内部微分へ送る。
方針：theta の一段下降と零段階での消滅を層射影へ適用する。
規約：元の高次 HA 成分を含む実正規化微分を使う。
使われ方：段階商と内部複体の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarLayerProjection_theta_zero (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarNormalizedGraded R D G))
    (hz : z ∈ dgCoherentBarNormalizedDegreeFiltration R D G x q n) :
    (moduleDegreeEvaluation R D x (q + 1)).map (dgCoherentBarLayerProjection R D G n)
      ((((moduleHomπ R D
        (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G))
        (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G)) x).f 1
          (dgCoherentBarNormalizedTheta R D G)).v q (q + 1) rfl) z) = 0 := by
  cases n with
  | zero => rw [dgCoherentBarNormalizedDegreeFiltration_zero_theta R D G x q z hz, map_zero]
  | succ n =>
    exact dgCoherentBarLayerProjection_annihilate R D G x (q + 1) (by omega)
      _ (dgCoherentBarNormalizedDegreeFiltration_theta R D G x q (n + 1) z hz)

lemma dgCoherentBarLayerProjection_d (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarNormalizedGraded R D G))
    (hz : z ∈ dgCoherentBarNormalizedDegreeFiltration R D G x q n) :
    ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G n)).d q (q + 1)
      ((moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerProjection R D G n) z) =
    (moduleDegreeEvaluation R D x (q + 1)).map (dgCoherentBarLayerProjection R D G n)
      (((dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).d
        q (q + 1) z) := by
  have h := ConcreteCategory.congr_hom
    (((moduleEvaluation R D x).map (dgCoherentBarLayerProjection R D G n)).comm q (q + 1)) z
  have hd := congrArg (fun f => f z)
    (dgCoherentBarNormalizedModule_d R D G (dgCoherentBarMaurerCartan_unconditional R D G)
      (Opposite.op x) q)
  change _ = ((moduleEvaluation R D x).obj
    (dgCoherentBarNormalizedGraded R D G)).d q (q + 1) z + _ at hd
  rw [hd, map_add, dgCoherentBarLayerProjection_theta_zero R D G x q n z hz, add_zero]
  exact h

def dgCoherentBarStageToLayer (x : D) (n : ℕ) :
    dgCoherentBarNormalizedStageComplex R D G x n ⟶
      (moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G n) :=
  CochainComplex.ofHom (fun q =>
    (dgCoherentBarNormalizedStageInclusion R D G x n).f q ≫
      (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerProjection R D G n)) (fun q => by
    erw [← Category.assoc
      ((dgCoherentBarNormalizedStageComplex R D G x n).d q (q + 1))
      ((dgCoherentBarNormalizedStageInclusion R D G x n).f (q + 1))
      ((moduleDegreeEvaluation R D x (q + 1)).map (dgCoherentBarLayerProjection R D G n)),
      ← (dgCoherentBarNormalizedStageInclusion R D G x n).comm q (q + 1)]
    ext z
    exact dgCoherentBarLayerProjection_d R D G x q n z.val z.property)

end SerrePositivity.InfinityCategories

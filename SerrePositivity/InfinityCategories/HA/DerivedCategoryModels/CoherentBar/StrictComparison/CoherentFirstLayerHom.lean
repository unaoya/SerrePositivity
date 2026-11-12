module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentFirstClosed
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentDimensionLayers

/-!
概要：各内部次元層から直下層への閉じた次数一の実作用素。
方針：一次列を正規化射影と層射影へ送り、実余積の全 Hom 同型で貼り合わせる。
規約：内部微分に関する閉性を主張し、実摂動微分の置換とはしない。
使われ方：実一次ホモロジー微分の鎖レベルの係数。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarLayerFirstCoefficient (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerIndex I (n + 1)) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G (n + 1) s))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n))).X 1 := by
  rcases s with ⟨⟨⟨m, t⟩, ht⟩, h⟩
  change m = n + 1 at h
  subst m
  exact (eHomWhiskerLeft (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G ⟨n + 1, t⟩)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G n)).f 1
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstColumn R D G t)

lemma dgCoherentBarLayerFirstCoefficient_d (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerIndex I (n + 1)) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G (n + 1) s))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n))).d 1 2
        (dgCoherentBarLayerFirstCoefficient R D G n s) = 0 := by
  rcases s with ⟨⟨⟨m, t⟩, ht⟩, h⟩
  change m = n + 1 at h
  subst m
  dsimp only [dgCoherentBarLayerFirstCoefficient]
  erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictHom_postcompose_d R D, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarFirstColumn_d, map_zero]

def dgCoherentBarLayerHomEquiv (n : ℕ) (N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (q : ℤ) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)).X q ≃ₗ[R]
    (∀ s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerIndex I n,
      (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G n s))
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)).X q) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCoproductHomDegreeIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G n) N q).toLinearEquiv

lemma dgCoherentBarLayerHomEquiv_apply (n : ℕ) (N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n))
      (ForgetEnrichment.to (Complex R) N)).X q) (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerIndex I n) :
    dgCoherentBarLayerHomEquiv R D G n N q z s =
      (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G n) s) N).f q z :=
  ConcreteCategory.congr_hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCoproductHomDegreeIso_π R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G n) N q s) z

def dgCoherentBarLayerFirstHom (n : ℕ) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G (n + 1)))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n))).X 1 :=
  (dgCoherentBarLayerHomEquiv R D G (n + 1) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n) 1).symm
    (dgCoherentBarLayerFirstCoefficient R D G n)

lemma dgCoherentBarLayerFirstHom_restrict (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerIndex I (n + 1)) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G (n + 1)) s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n)).f 1 (dgCoherentBarLayerFirstHom R D G n) =
    dgCoherentBarLayerFirstCoefficient R D G n s := by
  rw [← dgCoherentBarLayerHomEquiv_apply]
  exact congrFun ((dgCoherentBarLayerHomEquiv R D G (n + 1)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n) 1).apply_symm_apply _) s

set_option maxHeartbeats 800000 in
-- 余積 Hom の次数同型と実制限射を照合する局所上限。
lemma dgCoherentBarLayerFirstHom_d (n : ℕ) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G (n + 1)))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n))).d 1 2
        (dgCoherentBarLayerFirstHom R D G n) = 0 := by
  apply (dgCoherentBarLayerHomEquiv R D G (n + 1) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n) 2).injective
  rw [map_zero]
  funext s
  rw [dgCoherentBarLayerHomEquiv_apply]
  have h := ConcreteCategory.congr_hom ((eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G (n + 1)) s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n)).comm 1 2) (dgCoherentBarLayerFirstHom R D G n)
  have hclosed : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G (n + 1) s))
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n))).d 1 2
      ((eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G (n + 1)) s)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n)).f 1 (dgCoherentBarLayerFirstHom R D G n)) = 0 := by
    rw [dgCoherentBarLayerFirstHom_restrict, dgCoherentBarLayerFirstCoefficient_d]
  exact h.symm.trans hclosed

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

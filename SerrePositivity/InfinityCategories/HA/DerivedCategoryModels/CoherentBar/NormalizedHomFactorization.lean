module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedHomotopyImage
/-!
概要：退化因子への制限が零の全次数 Hom は、同じ非退化直和への射影を通る。
方針：元の全単体の Hom 直積同値で判定し、各包含と正規化射影の合成を照合する。
規約：閉次数零に限らず、全 dg 自然な斉次要素を扱う。
使われ方：theta の正規化商への降下と、商微分の MC 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open HomologicalComplex CochainComplex HomComplex
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgCoherentBarHom_precompose_comp {A B C N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (f : A ⟶ B) (g : B ⟶ C) (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) C)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)).X q) :
    (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) f N).f q
      ((eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) g N).f q z) =
    (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (f ≫ g) N).f q z := by
  have h := congrArg (fun a => a.f q z) (eHomWhiskerRight_comp (_root_.SerrePositivity.DifferentialGraded.Complex R) f g N)
  exact h.symm

private lemma preZero (M N P : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) P)).X q) :
    (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) (0 : M ⟶ N) P).f q z = 0 := by
  apply _root_.SerrePositivity.DifferentialGraded.moduleHomElement_ext R D
    (M := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M) (N := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) P)
  intro x
  rw [_root_.SerrePositivity.DifferentialGraded.moduleHomWhiskerRight_apply_π]
  have hz : (_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (0 : M ⟶ N) = 0 :=
    (_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map_zero M N
  rw [hz, Cochain.ofHom_zero, Cochain.zero_comp, map_zero]

variable {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarHom_factor_normalized (N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (q : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) N)).X q)
    (hz : ∀ s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarDegenerateIndex I,
      (eHomWhiskerRight (Complex R) (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val) N).f q z = 0) :
    (eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D F) N).f q
      ((eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedInclusion R D F) N).f q z) = z := by
  classical
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv R D F N q).injective
  funext s
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv_apply, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarHomEquiv_apply,
    dgCoherentBarHom_precompose_comp R D]
  by_cases hs : s.2 ∈ I.nonDegenerate s.1
  · have hi := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι R D F ⟨s, hs⟩
    rw [hi, dgCoherentBarHom_precompose_comp R D, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedInclusion_ι]
  · have hd : s.2 ∈ I.degenerate s.1 := by
      simpa only [SSet.nonDegenerate, Set.mem_compl_iff, not_not] using hs
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι_degenerate R D F ⟨s, hd⟩,
      preZero R D, hz ⟨s, hd⟩]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

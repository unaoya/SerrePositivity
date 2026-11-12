module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentDegreeDifferential

/-!
概要：単体次元零では実 coherent theta が消える。
方針：元の零単体列が零であることを各次数の実余積の支持へ延ばす。
規約：正規化射影との可換性で同じ実正規化 bar に移す。
使われ方：零段階の内部ホモロジーと、頂点からの標準比較。
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

set_option maxHeartbeats 800000 in
-- 元の Hom end と次数評価の支持を照合する局所上限。
lemma dgCoherentBarDegreeFiltration_zero_theta (x : D) (q : ℤ)
    (z : (moduleDegreeEvaluation R D x q).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G))
    (hz : z ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarDegreeFiltration R D G x q 0) :
    (((moduleHomπ R D (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G)) x).f 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D G)).v q (q + 1) rfl) z = 0 := by
  refine Submodule.iSup_induction
    (motive := fun z => (((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D G)) x).f 1
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D G)).v q (q + 1) rfl) z = 0)
    (fun s : {s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I // s.1 ≤ 0} =>
      LinearMap.range ((_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).map
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s.val)).hom) hz ?_ ?_ ?_
  · rintro ⟨⟨n, s⟩, hn⟩ a ⟨b, rfl⟩
    have hn' : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomogeneous_pre_apply R D
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) ⟨0, s⟩) 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D G) x q b,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_restrict R D G ⟨0, s⟩, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn]
    simp only [map_zero, Cochain.zero_v]
    rfl
  · exact map_zero _
  · intro a b ha hb
    rw [map_add, ha, hb, add_zero]

set_option maxHeartbeats 800000 in
-- 同じ正規化射影と Hom end の次数評価に限った局所上限。
lemma dgCoherentBarNormalizedDegreeFiltration_zero_theta (x : D) (q : ℤ)
    (z : (moduleDegreeEvaluation R D x q).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G))
    (hz : z ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q 0) :
    (((_root_.SerrePositivity.DifferentialGraded.moduleHomπ R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G)) x).f 1
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta R D G)).v q (q + 1) rfl) z = 0 := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
  erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomogeneous_pre_apply R D
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G) 1 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta R D G) x q a,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedTheta_projection R D G, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomogeneous_post_apply R D,
    dgCoherentBarDegreeFiltration_zero_theta R D G x q a ha, map_zero]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

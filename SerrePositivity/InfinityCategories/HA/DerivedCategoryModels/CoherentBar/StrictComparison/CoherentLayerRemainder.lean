module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerSurjectivity

/-!
概要：最高単体次元の射影を除くと、同じ元の支持が一段下がる。
方針：実余積の各ラベルで、最高次元では分裂、低次元では射影零を使う。
規約：元の次数付き元そのものの分解を保持する。
使われ方：段階商の核の同定と有限 support の下降。
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

lemma dgCoherentBarLayerRemainder_mem (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G))
    (hz : z ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q (n + 1)) :
    z - (moduleDegreeEvaluation R D x q).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G (n + 1))
      ((moduleDegreeEvaluation R D x q).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G (n + 1)) z) ∈
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q n := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
  let E := _root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q
  let p := E.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G)
  let l := E.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G (n + 1))
  let i := E.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerInclusion R D G (n + 1))
  change p a - i (l (p a)) ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q n
  refine Submodule.iSup_induction
    (motive := fun a => p a - i (l (p a)) ∈
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q n)
    (fun s : {s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I // s.1 ≤ n + 1} =>
      LinearMap.range (E.map (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s.val)).hom) ha ?_ ?_ ?_
  · intro s a ha
    obtain ⟨b, rfl⟩ := ha
    by_cases hs : s.val.1 = n + 1
    · have h := congrArg (fun f => E.map f b)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection_raw_ι_of_eq R D G (n + 1) s.val hs)
      have h' : i (l (p (E.map (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s.val) b))) =
          p (E.map (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s.val) b) := by
        simpa only [E, p, l, i, CategoryTheory.Functor.map_comp, ModuleCat.comp_apply] using! h
      rw [h', sub_self]
      exact Submodule.zero_mem _
    · have hlt : s.val.1 < n + 1 := lt_of_le_of_ne s.property hs
      have h := congrArg (fun f => E.map f b)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection_raw_ι_of_lt R D G (n + 1) s.val hlt)
      have h' : l (p (E.map (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s.val) b)) = 0 := by
        simpa only [E, p, l, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_zero,
          ModuleCat.comp_apply] using! h
      rw [h', map_zero, sub_zero]
      exact Submodule.mem_map.mpr ⟨_,
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarDegreeFiltration_inclusion R D G x q n s.val (by omega) b, rfl⟩
  · simp only [map_zero, sub_self]
    exact Submodule.zero_mem _
  · intro a b ha hb
    simpa only [map_add, add_sub_add_comm] using Submodule.add_mem
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q n) ha hb

lemma dgCoherentBarLayerProjection_kernel_mem (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G))
    (hz : z ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q (n + 1))
    (hp : (moduleDegreeEvaluation R D x q).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerProjection R D G (n + 1)) z = 0) :
    z ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q n := by
  have h := dgCoherentBarLayerRemainder_mem R D G x q n z hz
  rw [hp, map_zero, sub_zero] at h
  exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

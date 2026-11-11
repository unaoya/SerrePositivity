module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentStageHomologySupport

/-!
概要：零段階のホモロジー類が実 bar で零なら、ある有限段階ですでに零である。
方針：実境界の primitive の有限 support を取り、包含の単射性で境界式を反映する。
規約：全 HA 成分を持つ実複体で判定し、filtered 性を仮定しない。
使われ方：最終ホモロジーの核を隣接段階の長完全列で下降させる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarZeroStageHomology_finiteKernel (x : D) (q : ℤ)
    (a : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x 0).homology q)
    (ha : HomologicalComplex.homologyMap
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x 0) q a = 0) :
    ∃ m : ℕ, HomologicalComplex.homologyMap
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap R D G x (Nat.zero_le m)) q a = 0 := by
  let K := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)
  let K₀ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x 0
  let i₀ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x 0
  obtain ⟨z, hz, rfl⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass_surjective R K₀ q a
  have hzK : K.d q (q + 1) (i₀.f q z) = 0 := by
    have h := ConcreteCategory.congr_hom (i₀.comm q (q + 1)) z
    change K.d q (q + 1) (i₀.f q z) = i₀.f (q + 1) (K₀.d q (q + 1) z) at h
    rw [hz, map_zero] at h
    exact h
  have hclass : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass R K q (i₀.f q z) hzK = 0 := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass_map R i₀ q z hz hzK]
    exact ha
  obtain ⟨y, hy⟩ := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass_eq_zero_iff R K q _ hzK).mp hclass
  obtain ⟨m, b, hb⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStages_exhaustive R D G x (q - 1) y
  let Km := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x m
  let im := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x m
  let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap R D G x (Nat.zero_le m)
  have hdy : Km.d (q - 1) q b = f.f q z := by
    apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStageInclusion_injective R D G x m q
    have h := ConcreteCategory.congr_hom (im.comm (q - 1) q) b
    change K.d (q - 1) q (im.f (q - 1) b) = im.f q (Km.d (q - 1) q b) at h
    change im.f (q - 1) b = y at hb
    rw [hb, hy] at h
    have hf := ConcreteCategory.congr_hom
      (congrArg (fun g => g.f q) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap_inclusion
        R D G x (Nat.zero_le m))) z
    exact h.symm.trans hf.symm
  have hz' : Km.d q (q + 1) (f.f q z) = 0 := by
    have h := ConcreteCategory.congr_hom (f.comm q (q + 1)) z
    change Km.d q (q + 1) (f.f q z) = f.f (q + 1) (K₀.d q (q + 1) z) at h
    rw [hz, map_zero] at h
    exact h
  refine ⟨m, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass_map R f q z hz hz']
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass_eq_zero_iff R Km q _ hz').mpr ⟨b, hdy⟩

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

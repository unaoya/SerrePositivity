module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexHomologyClassBoundary
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentStages

/-!
概要：実正規化 bar の全ホモロジー類は有限段階から来る。
方針：cycle の有限 support を持ち上げ、次数ごとの包含の単射性で閉性を反映する。
規約：全 HA 成分を含む実微分と非有界整数次数を使う。
使われ方：一次完全性による有限段階からの下降。
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

lemma dgCoherentBarStageInclusion_injective (x : D) (n : ℕ) (q : ℤ) :
    Function.Injective ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x n).f q) :=
  Subtype.val_injective

@[reassoc]
lemma dgCoherentBarStageMap_comp (x : D) {l n m : ℕ} (h₁ : l ≤ n) (h₂ : n ≤ m) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap R D G x h₁ ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap R D G x h₂ =
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageMap R D G x (h₁.trans h₂) := by
  ext q z
  rfl

lemma dgCoherentBarStageHomology_exhaustive (x : D) (q : ℤ)
    (a : ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).homology q) :
    ∃ (n : ℕ) (b : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x n).homology q),
      HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x n) q b = a := by
  let K := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)
  obtain ⟨z, hz, rfl⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass_surjective R K q a
  obtain ⟨n, b, hb⟩ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStages_exhaustive R D G x q z
  let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D G x n
  have hbz : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x n).d q (q + 1) b = 0 := by
    apply dgCoherentBarStageInclusion_injective R D G x n (q + 1)
    have h := ConcreteCategory.congr_hom (f.comm q (q + 1)) b
    change K.d q (q + 1) (f.f q b) =
      f.f (q + 1) ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageComplex R D G x n).d q (q + 1) b) at h
    rw [hb, hz] at h
    simpa only [map_zero] using! h.symm
  refine ⟨n, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass R _ q b hbz, ?_⟩
  have hb' : K.d q (q + 1) (f.f q b) = 0 := by rw [hb]; exact hz
  change f.f q b = z at hb
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyClass_map R f q b hbz hb'
  simpa only [hb] using! h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerAnnihilation

/-!
概要：正規化 bar の単体次元上限を持つ因子の実 dg 直和と、その分裂した包含。
方針：同じ非退化添字の部分族を取り、次数上限の判定で元の直和から射影する。
規約：この葉では内部微分を持つ graded bar を扱い、θ の制限は後続で構成する。
使われ方：実 dg 加群の段階模型と h-projective 性の帰納。
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

abbrev dgCoherentBarCutIndex (n : ℕ) := {s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I // s.val.1 ≤ n}
abbrev dgCoherentBarCutFamily (n : ℕ) (s : dgCoherentBarCutIndex (I := I) n) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D G s.val
abbrev dgCoherentBarCutGraded (n : ℕ) : ModuleCategory R D := ∐ dgCoherentBarCutFamily R D G n

def dgCoherentBarCutInclusion (n : ℕ) :
    dgCoherentBarCutGraded R D G n ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G :=
  Sigma.desc (fun s => Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D G) s.val)

def dgCoherentBarCutProjection (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G ⟶ dgCoherentBarCutGraded R D G n := by
  classical
  exact Sigma.desc (fun s => if h : s.val.1 ≤ n then
    Sigma.ι (dgCoherentBarCutFamily R D G n) ⟨s, h⟩ else 0)

@[reassoc (attr := simp)]
lemma dgCoherentBarCutInclusion_ι (n : ℕ) (s : dgCoherentBarCutIndex (I := I) n) :
    Sigma.ι (dgCoherentBarCutFamily R D G n) s ≫ dgCoherentBarCutInclusion R D G n =
      Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D G) s.val := by
  simp only [dgCoherentBarCutInclusion, Sigma.ι_comp_desc]

@[reassoc (attr := simp)]
lemma dgCoherentBarCutProjection_ι (n : ℕ) (s : dgCoherentBarCutIndex (I := I) n) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D G) s.val ≫ dgCoherentBarCutProjection R D G n =
      Sigma.ι (dgCoherentBarCutFamily R D G n) s := by
  classical
  simp only [dgCoherentBarCutProjection, Sigma.ι_comp_desc, dif_pos s.property]

lemma dgCoherentBarCutInclusion_projection (n : ℕ) :
    dgCoherentBarCutInclusion R D G n ≫ dgCoherentBarCutProjection R D G n = 𝟙 _ := by
  apply Sigma.hom_ext
  intro s
  rw [dgCoherentBarCutInclusion_ι_assoc, dgCoherentBarCutProjection_ι, Category.comp_id]

lemma dgCoherentBarCutProjector_raw_ι (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I) (hs : s.1 ≤ n) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G ≫
      dgCoherentBarCutProjection R D G n ≫ dgCoherentBarCutInclusion R D G n =
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G := by
  classical
  by_cases h : s.2 ∈ I.nonDegenerate s.1
  · rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι_assoc R D G ⟨s, h⟩,
      dgCoherentBarCutProjection_ι_assoc R D G n ⟨⟨s, h⟩, hs⟩,
      dgCoherentBarCutInclusion_ι]
    exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι R D G ⟨s, h⟩).symm
  · have hd : s.2 ∈ I.degenerate s.1 := by
      simpa only [SSet.nonDegenerate, Set.mem_compl_iff, not_not] using h
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι_degenerate_assoc R D G ⟨s, hd⟩,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι_degenerate R D G ⟨s, hd⟩]
    simp only [zero_comp]

lemma dgCoherentBarCutProjector_recover (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G))
    (hz : z ∈ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedDegreeFiltration R D G x q n) :
    (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).map
      (dgCoherentBarCutProjection R D G n ≫ dgCoherentBarCutInclusion R D G n) z = z := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
  let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G ≫
    dgCoherentBarCutProjection R D G n ≫ dgCoherentBarCutInclusion R D G n -
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G
  have hf : ∀ s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I, s.1 ≤ n →
      Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s ≫ f = 0 := by
    intro s hs
    dsimp only [f]
    rw [Preadditive.comp_sub, dgCoherentBarCutProjector_raw_ι R D G n s hs, sub_self]
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarDegreeFiltration_annihilate R D G f x q n hf a ha
  change (_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).map f a = 0 at h
  change ((_root_.SerrePositivity.DifferentialGraded.moduleDegreeEvaluation R D x q).map f).hom a = 0 at h
  simpa only [f, CategoryTheory.Functor.map_sub, CategoryTheory.Functor.map_comp,
    ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.comp_apply, sub_eq_zero] using! h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

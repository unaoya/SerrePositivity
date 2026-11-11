module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentDegreeFiltration

/-!
概要：実正規化 bar の単体次元ごとの内部複体を取り出す。
方針：指定次元の非退化ラベルの直和と、その包含・射影を作る。
規約：この葉の射は内部微分について閉じた射。実 theta との関係は別に示す。
使われ方：単体次元フィルトレーションの段階商の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial

abbrev dgCoherentBarLayerIndex (I : SSet.{u}) (n : ℕ) :=
  {s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I // s.val.1 = n}

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

abbrev dgCoherentBarLayerFamily (n : ℕ) (s : dgCoherentBarLayerIndex I n) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D G s.val

abbrev dgCoherentBarLayerGraded (n : ℕ) : ModuleCategory R D :=
  ∐ dgCoherentBarLayerFamily R D G n

def dgCoherentBarLayerInclusion (n : ℕ) :
    dgCoherentBarLayerGraded R D G n ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G :=
  Sigma.desc (fun s => Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D G) s.val)

def dgCoherentBarLayerProjection (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D G ⟶ dgCoherentBarLayerGraded R D G n := by
  classical
  exact Sigma.desc (fun s => if h : s.val.1 = n then
    Sigma.ι (dgCoherentBarLayerFamily R D G n) ⟨s, h⟩ else 0)

@[reassoc (attr := simp)]
lemma dgCoherentBarLayerInclusion_ι (n : ℕ) (s : dgCoherentBarLayerIndex I n) :
    Sigma.ι (dgCoherentBarLayerFamily R D G n) s ≫ dgCoherentBarLayerInclusion R D G n =
      Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D G) s.val := by
  simp only [dgCoherentBarLayerInclusion, Sigma.ι_comp_desc]

@[reassoc (attr := simp)]
lemma dgCoherentBarLayerProjection_ι (n : ℕ) (s : dgCoherentBarLayerIndex I n) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D G) s.val ≫ dgCoherentBarLayerProjection R D G n =
      Sigma.ι (dgCoherentBarLayerFamily R D G n) s := by
  classical
  simp only [dgCoherentBarLayerProjection, Sigma.ι_comp_desc, dite_eq_left s.property]

lemma dgCoherentBarLayerProjection_ι_of_ne (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex I)
    (hs : s.val.1 ≠ n) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D G) s ≫ dgCoherentBarLayerProjection R D G n = 0 := by
  classical
  simp only [dgCoherentBarLayerProjection, Sigma.ι_comp_desc, dite_eq_right hs]

lemma dgCoherentBarLayerInclusion_projection (n : ℕ) :
    dgCoherentBarLayerInclusion R D G n ≫ dgCoherentBarLayerProjection R D G n = 𝟙 _ := by
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc, dgCoherentBarLayerInclusion_ι, dgCoherentBarLayerProjection_ι,
    Category.comp_id]

lemma dgCoherentBarLayerProjection_raw_ι_of_lt (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I)
    (hs : s.1 < n) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n = 0 := by
  classical
  by_cases h : s.2 ∈ I.nonDegenerate s.1
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι R D G ⟨s, h⟩]
    exact dgCoherentBarLayerProjection_ι_of_ne R D G n ⟨s, h⟩ (Nat.ne_of_lt hs)
  · simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection, Sigma.ι_comp_desc_assoc, dite_eq_right h,
      zero_comp]

lemma dgCoherentBarLayerProjection_raw_ι_of_eq (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I)
    (hs : s.1 = n) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G ≫
      dgCoherentBarLayerProjection R D G n ≫ dgCoherentBarLayerInclusion R D G n =
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G := by
  classical
  by_cases h : s.2 ∈ I.nonDegenerate s.1
  · erw [← Category.assoc (Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D G) s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection R D G),
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection_ι R D G ⟨s, h⟩]
    rw [← Category.assoc, dgCoherentBarLayerProjection_ι R D G n ⟨⟨s, h⟩, hs⟩,
      dgCoherentBarLayerInclusion_ι]
  · simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedProjection, Sigma.ι_comp_desc_assoc,
      Sigma.ι_comp_desc, dite_eq_right h, zero_comp]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

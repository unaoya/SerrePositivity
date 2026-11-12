module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Module
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
/-!
概要：退化単体を除いた同じ係数族の直和と、元の graded bar との分裂を作る。
方針：Mathlib の nonDegenerate をラベルに使い、直和の普遍性で包含と射影を作る。
規約：この段階の射は元の内部微分に対する射。theta を加えた微分との可換性は別に検証する。
使われ方：正規化 bar の係数模型、退化部分の縮約と変形 retract の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial

abbrev dgCoherentBarNormalizedIndex (I : SSet.{u}) :=
  {s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I // s.2 ∈ I.nonDegenerate s.1}

abbrev dgCoherentBarDegenerateIndex (I : SSet.{u}) :=
  {s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I // s.2 ∈ I.degenerate s.1}

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

abbrev dgCoherentBarNormalizedFamily (s : dgCoherentBarNormalizedIndex I) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F s.val

abbrev dgCoherentBarNormalizedGraded : ModuleCategory R D :=
  ∐ dgCoherentBarNormalizedFamily R D F

def dgCoherentBarNormalizedInclusion :
    dgCoherentBarNormalizedGraded R D F ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F :=
  Sigma.desc (fun s => Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val)

def dgCoherentBarNormalizedProjection :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F ⟶ dgCoherentBarNormalizedGraded R D F := by
  classical
  exact Sigma.desc (fun s => if h : s.2 ∈ I.nonDegenerate s.1 then
    Sigma.ι (dgCoherentBarNormalizedFamily R D F) ⟨s, h⟩ else 0)

@[reassoc (attr := simp)]
lemma dgCoherentBarNormalizedInclusion_ι (s : dgCoherentBarNormalizedIndex I) :
    Sigma.ι (dgCoherentBarNormalizedFamily R D F) s ≫
      dgCoherentBarNormalizedInclusion R D F =
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val := by
  simp [dgCoherentBarNormalizedInclusion]

@[reassoc (attr := simp)]
lemma dgCoherentBarNormalizedProjection_ι (s : dgCoherentBarNormalizedIndex I) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val ≫
      dgCoherentBarNormalizedProjection R D F =
    Sigma.ι (dgCoherentBarNormalizedFamily R D F) s := by
  classical
  simp [dgCoherentBarNormalizedProjection, s.property]

@[reassoc (attr := simp)]
lemma dgCoherentBarNormalizedProjection_ι_degenerate (s : dgCoherentBarDegenerateIndex I) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F) s.val ≫
      dgCoherentBarNormalizedProjection R D F = 0 := by
  classical
  simp [dgCoherentBarNormalizedProjection, SSet.nonDegenerate, s.property]

lemma dgCoherentBarNormalizedInclusion_projection :
    dgCoherentBarNormalizedInclusion R D F ≫
      dgCoherentBarNormalizedProjection R D F = 𝟙 _ := by
  apply Sigma.hom_ext
  intro s
  rw [← Category.assoc, dgCoherentBarNormalizedInclusion_ι,
    dgCoherentBarNormalizedProjection_ι, Category.comp_id]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

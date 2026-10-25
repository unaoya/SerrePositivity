module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Module
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

abbrev dgCoherentBarNormalizedIndex (I : SSet.{u}) :=
  {s : dgCoherentBarIndex I // s.2 ∈ I.nonDegenerate s.1}

abbrev dgCoherentBarDegenerateIndex (I : SSet.{u}) :=
  {s : dgCoherentBarIndex I // s.2 ∈ I.degenerate s.1}

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

abbrev dgCoherentBarNormalizedFamily (s : dgCoherentBarNormalizedIndex I) :=
  dgCoherentBarFamily R D F s.val

abbrev dgCoherentBarNormalizedGraded : ModuleCategory R D :=
  ∐ dgCoherentBarNormalizedFamily R D F

def dgCoherentBarNormalizedInclusion :
    dgCoherentBarNormalizedGraded R D F ⟶ dgCoherentBarGraded R D F :=
  Sigma.desc (fun s => Sigma.ι (dgCoherentBarFamily R D F) s.val)

def dgCoherentBarNormalizedProjection :
    dgCoherentBarGraded R D F ⟶ dgCoherentBarNormalizedGraded R D F := by
  classical
  exact Sigma.desc (fun s => if h : s.2 ∈ I.nonDegenerate s.1 then
    Sigma.ι (dgCoherentBarNormalizedFamily R D F) ⟨s, h⟩ else 0)

@[reassoc (attr := simp)]
lemma dgCoherentBarNormalizedInclusion_ι (s : dgCoherentBarNormalizedIndex I) :
    Sigma.ι (dgCoherentBarNormalizedFamily R D F) s ≫
      dgCoherentBarNormalizedInclusion R D F =
    Sigma.ι (dgCoherentBarFamily R D F) s.val := by
  simp [dgCoherentBarNormalizedInclusion]

@[reassoc (attr := simp)]
lemma dgCoherentBarNormalizedProjection_ι (s : dgCoherentBarNormalizedIndex I) :
    Sigma.ι (dgCoherentBarFamily R D F) s.val ≫
      dgCoherentBarNormalizedProjection R D F =
    Sigma.ι (dgCoherentBarNormalizedFamily R D F) s := by
  classical
  simp [dgCoherentBarNormalizedProjection, s.property]

@[reassoc (attr := simp)]
lemma dgCoherentBarNormalizedProjection_ι_degenerate (s : dgCoherentBarDegenerateIndex I) :
    Sigma.ι (dgCoherentBarFamily R D F) s.val ≫
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

end SerrePositivity.InfinityCategories

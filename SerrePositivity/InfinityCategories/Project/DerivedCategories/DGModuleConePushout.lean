module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleConeBoundaryJoinFaces

/-! # 標準 cofiber 余錐の普遍性

概要：全 Hom end を持つ dg 加群の nerve の標準 cone 四角形の押し出し性を証明する。
方針：指定余錐を最初の頂点に持つ全ての coslice 境界を、二セルの明示解で直接充填する。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：β3 の dg 加群模型の cofiber と安定性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 標準 cofiber 余錐は coslice の始対象である。 -/
lemma dgModuleConeCocone_isColimit (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D f) := by
  intro n b hb
  let F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryJoinFiller A D f b hb
  have hfaces := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeBoundaryJoinFiller_faces A D f b hb
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cosliceJoinBoundaryFaces_fixed _ b F hfaces), ?_⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceUnderCurry_boundary_of_joinFaces _ b F hfaces

/-- 標準 mapping cone による cofiber 正方形は実際の ∞ 押し出しである。 -/
lemma dgModuleConeSquare_isPushout (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f) :=
  dgModuleConeCocone_isColimit A D f

end SerrePositivity.InfinityCategories.Project.DerivedCategories

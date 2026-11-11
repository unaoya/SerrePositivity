module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveConeComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanBoundary
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FiniteShapes
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagramEvaluation

/-!
概要：元の pullback 錐を穿孔 core へ延長し、外側の錐と実比較辺を作る。
方針：同じ native 錐の厳密な制限と頂点を保持する。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ と合成式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma pullbackCone_vertex {X : SSet.{u}} (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone Q).vertex = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex Q 0 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (horn 2 2 : SSet.{u}) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ Q)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cospanConeSquareIso_initialPoint,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

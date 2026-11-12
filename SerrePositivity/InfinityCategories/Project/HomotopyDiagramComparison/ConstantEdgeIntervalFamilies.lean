module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.ConstantEdgeFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LeftTransport

/-!
概要：元の一本の辺の定値パラメータ族と、二端点の積への制限を厳密に計算する。
方針：元の区間族と元の辺 prism の端点公式を再利用する。
規約：同じ元の辺の一単体を保持し、Hom 類の一致に弱めない。
使われ方：Yoneda 評価の底方向自然性の元の四辺の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 一本の元の辺の定値区間族は、同じ元の辺 prism。 -/
lemma intervalMappingUncurry_const_edge {K X : SSet.{u}} {a b : X _⦋0⦌}
    (e : SSet.Edge a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e)) =
      fst (Δ[1] : SSet.{u}) K ≫ SSet.yonedaEquiv.symm e.edge := by
  apply (cancel_epi (β_ K (Δ[1] : SSet.{u})).hom).mp
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e))).h = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.intervalFamilyHomotopy_const_edge_h]
  rfl

/-- 元の辺を第一因子に作用させた prism の始点は、元の同じ始点との積。 -/
lemma edgePrism_start_tensor {K X : SSet.{u}} {a b : X _⦋0⦌} (e : SSet.Edge a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ (SSet.yonedaEquiv.symm e.edge ▷ K) =
      lift (SSet.const a) (𝟙 K) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerRight_fst, lift_fst]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_zero e.edge).trans (congrArg SSet.const e.src_eq)
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl

/-- 元の辺を第一因子に作用させた prism の終点は、元の同じ終点との積。 -/
lemma edgePrism_finish_tensor {K X : SSet.{u}} {a b : X _⦋0⦌} (e : SSet.Edge a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ (SSet.yonedaEquiv.symm e.edge ▷ K) =
      lift (SSet.const b) (𝟙 K) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerRight_fst, lift_fst]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEdgeFamily_one e.edge).trans (congrArg SSet.const e.tgt_eq)
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro k
    rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

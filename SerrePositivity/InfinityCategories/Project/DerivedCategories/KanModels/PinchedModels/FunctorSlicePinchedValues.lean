module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorSliceRepresentation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.SliceEvaluationPinched
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ConstantHomotopyComponent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.TerminalConeSectionEdges
/-!
概要：任意に選んだ全錐による関手圏の slice 表示は、元の実 pinched Hom 族の値を保つ。
方針：同じ切断辺の底への像を、普遍評価の自然性と恒等錐成分で照合する。
規約：全パラメータと切断の選択全てで成立する。使われ方：実屋根の評価の比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- どの全切断による slice 表示でも、実 pinched Hom 族は元の同じ関手圏の射を表す。 -/
lemma roofFunctorSliceRepresentation_pinched_vertex_arrow {K X : SSet.{u}} [Quasicategory X]
    {y z : X _⦋0⦌} (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorSliceRepresentation K z) (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y z) :
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge
      ((SSet.yonedaEquiv (X := (ihom K).obj X)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := K) z)))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofFunctorSliceRepresentationMap K z C).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice X y z))))) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace y z)) := by
  let p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceProjection K z
  let t := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity K z
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilySlice X y z)
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := K) z)
  have h₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofTerminalRepresentationMap_transport_vertex_arrow t C.coneSection
    C.coneSection_projection p (SSet.yonedaEquiv.symm b)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceIdentity_point K z) a
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofHomotopyToConstant_component_arrow b
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluationHomotopy K z)
    (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofTerminalConeSectionEdge t C.coneSection C.coneSection_projection a))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluation_identity_component_arrow K z)
  exact h₀.trans (h₁.trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Roof.roofFunctorSliceEvaluation_pinched_component_arrow f))
end SerrePositivity.InfinityCategories.Project.DerivedCategories

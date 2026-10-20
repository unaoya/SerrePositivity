module
public import SerrePositivity.InfinityCategories.Derived.FunctorSliceRepresentation
public import SerrePositivity.InfinityCategories.Derived.SliceEvaluationPinched
public import SerrePositivity.InfinityCategories.Derived.ConstantHomotopyComponent
public import SerrePositivity.InfinityCategories.Derived.TerminalConeSectionEdges
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
namespace SerrePositivity.InfinityCategories
/-- どの全切断による slice 表示でも、実 pinched Hom 族は元の同じ関手圏の射を表す。 -/
lemma roofFunctorSliceRepresentation_pinched_vertex_arrow {K X : SSet.{u}} [Quasicategory X]
    {y z : X _⦋0⦌} (C : FunctorSliceRepresentation K z) (f : K ⟶ pinchedHom y z) :
    Arrow.mk (Truncated.HomotopyCategory.homMk (roofPointSliceVertexEdge
      ((SSet.yonedaEquiv (X := (ihom K).obj X)).symm
        (functorVertex (SSet.const (X := K) z)))
      ((roofFunctorSliceRepresentationMap K z C).app (Opposite.op ⦋0⦌)
        (functorVertex (f ≫ pinchedFamilySlice X y z))))) =
      Arrow.mk (intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace y z)) := by
  let p := roofFunctorSliceProjection K z
  let t := roofFunctorSliceIdentity K z
  let a := functorVertex (f ≫ pinchedFamilySlice X y z)
  let b := functorVertex (SSet.const (X := K) z)
  have h₀ := roofTerminalRepresentationMap_transport_vertex_arrow t C.coneSection
    C.coneSection_projection p (SSet.yonedaEquiv.symm b)
    (roofFunctorSliceIdentity_point K z) a
  have h₁ := roofHomotopyToConstant_component_arrow b
    (roofFunctorSliceEvaluationHomotopy K z)
    (Truncated.HomotopyCategory.homMk
      (roofTerminalConeSectionEdge t C.coneSection C.coneSection_projection a))
    (roofFunctorSliceEvaluation_identity_component_arrow K z)
  exact h₀.trans (h₁.trans (roofFunctorSliceEvaluation_pinched_component_arrow f))
end SerrePositivity.InfinityCategories

module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalCoconeUnit
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentHomotopyVertex

/-!
概要：元の native 全空間余錐の単位を、同じ全空間射の指定表現として保持する。
方針：既存の native 単位比較を使い、頂点等式だけを型へ反映する。
規約：単位の全円柱を変更しない。使われ方：実際の自然性三角形への合成比較の適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 変換頂点を実円柱へ移してから戻すと、元の変換頂点そのもの。 -/
lemma coherentVertexOfHomotopy_of_vertex {K : SSet.{u + 1}}
    {F G : K ⟶ SpaceInfinity.{u}}
    (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) :
    coherentVertexOfHomotopy (simplicialHomotopyOfFunctorEdge
      (intervalMappingEdgeOfVertex t).toTruncated) = t := by
  apply (intervalMappingEdgeVertexEquiv (functorVertex F) (functorVertex G)).symm.injective
  apply SSet.Edge.ext
  change (intervalMappingEdgeOfVertex (coherentVertexOfHomotopy
    (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex t).toTruncated))).edge = _
  refine (coherentVertexOfHomotopy_edge _).trans ?_
  change SSet.yonedaEquiv (curry (uncurry
    (SSet.yonedaEquiv.symm (intervalMappingEdgeOfVertex t).edge))) = _
  rw [curry_uncurry, Equiv.apply_symm_apply]
  rfl

variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 元の native 余錐の単位自体が、元の具体的な全空間単位の指定表現。 -/
def coherentNativeUnitRepresentation : CoherentConstantRepresentation F
    (coherentDiagramTotalVertex F) (coherentDiagramTotalUnit F) :=
  ⟨(coconeTransformationMap F (coherentDiagramTotalVertex F)).app (Opposite.op ⦋0⦌)
    (coconeMappingPointAt (coherentDiagramTotalCocone F) (coherentDiagramTotalVertex F)
      (coherentDiagramTotalCocone_vertex F)), coherentTotalCoconeUnitIso F⟩

/-- 元の native 単位を、指定全空間頂点を標的に持つ同じ実円柱として読む。 -/
def coherentNativeUnitHomotopy : SSet.Homotopy F (SSet.const (coherentDiagramTotalVertex F)) :=
  simplicialHomotopyOfFunctorEdge
    (intervalMappingEdgeOfVertex (coherentNativeUnitRepresentation F).1).toTruncated

/-- 頂点等式の型への反映で、元の native 単位円柱の射は変わらない。 -/
lemma coherentNativeUnitHomotopy_h : (coherentNativeUnitHomotopy F).h =
    (coconeTransformationHomotopy (coherentDiagramTotalCocone F)).h := by
  have hgen {K X : SSet.{u + 1}} {f : K ⟶ X} (c : JoinCocone f)
      (z : X _⦋0⦌) (hv : c.vertex = z) :
      (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex
        ((coconeTransformationMap f z).app (Opposite.op ⦋0⦌)
          (coconeMappingPointAt c z hv))).toTruncated).h =
        (coconeTransformationHomotopy c).h := by
    subst z
    rfl
  exact hgen _ _ (coherentDiagramTotalCocone_vertex F)

end SerrePositivity.InfinityCategories.F2

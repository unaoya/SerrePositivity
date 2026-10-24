module
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningMappingSpace
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorUnitHom
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertices
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyRepresentative

/-! # 指定した coherent な二胞体を、同じ小さい unstraightening の底上の実写像へ移す -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {B : SSet.{u}}
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (a : FunctorHom F G)

/-- 元の二胞体を、同じ全関手空間内の一本の実辺で表示する。 -/
def smallUnstraighteningHomEdge : SSet.Edge (functorVertex F) (functorVertex G) :=
  SSet.Edge.ofTruncated (functorEdgeOfSimplicialHomotopy (functorHomHomotopy a))

/-- 代表辺の類は、指定した元の比較二胞体そのもの。 -/
theorem smallUnstraighteningHomEdge_hom :
    Truncated.HomotopyCategory.homMk (smallUnstraighteningHomEdge a).toTruncated = a :=
  functorHomHomotopy_hom a

/-- 元の二胞体の代表辺を、変換の実際の区間写像空間の点にする。 -/
def smallUnstraighteningHomParameter : (leftUnstraighteningTransformationSpace F G) _⦋0⦌ :=
  intervalMappingVertexOfEdge (smallUnstraighteningHomEdge a)

/-- 全写像空間の比較射の同じ値を、元の宇宙の相対関手の実頂点へ戻す。 -/
def smallUnstraighteningHomVertex :
    (relativeFunctorSpace (smallLeftUnstraighteningProjection G)
      (smallLeftUnstraighteningProjection F)) _⦋0⦌ :=
  ((liftedSmallLeftUnstraighteningMappingSpaceMap F G).app (Opposite.op ⦋0⦌)
    (smallUnstraighteningHomParameter a)).down

/-- 同じ二胞体に対する小さい unstraightening 間の底上の実写像。 -/
def smallUnstraighteningFunctorHom :
    smallLeftUnstraightening F ⟶ smallLeftUnstraightening G :=
  ((relativeFunctorVertexEquiv (smallLeftUnstraighteningProjection G)
    (smallLeftUnstraighteningProjection F)).symm (smallUnstraighteningHomVertex a)).val

/-- 構成した同じ実写像は、元の小さい底を厳密に保持する。 -/
theorem smallUnstraighteningFunctorHom_projection : smallUnstraighteningFunctorHom a ≫
    smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection F :=
  ((relativeFunctorVertexEquiv (smallLeftUnstraighteningProjection G)
    (smallLeftUnstraighteningProjection F)).symm (smallUnstraighteningHomVertex a)).property

/-- 実写像を相対関手の頂点へ戻すと、全写像空間の比較射で指定した同じ値を回収する。 -/
theorem smallUnstraighteningFunctorHom_vertex :
    relativeFunctorVertex (smallLeftUnstraighteningProjection G)
      (smallLeftUnstraighteningProjection F) (smallUnstraighteningFunctorHom a)
      (smallUnstraighteningFunctorHom_projection a) = smallUnstraighteningHomVertex a :=
  (relativeFunctorVertexEquiv (smallLeftUnstraighteningProjection G)
    (smallLeftUnstraighteningProjection F)).apply_symm_apply _

/-- 大きい相対写像空間へ移すと、元の全写像空間比較の同じ値そのものとなる。 -/
theorem smallUnstraighteningFunctorHom_recover :
    (smallLeftUnstraighteningRelativeFunctorIso F G).hom.app (Opposite.op ⦋0⦌)
      (ULift.up (relativeFunctorVertex (smallLeftUnstraighteningProjection G)
        (smallLeftUnstraighteningProjection F) (smallUnstraighteningFunctorHom a)
        (smallUnstraighteningFunctorHom_projection a))) =
      (leftUnstraighteningMappingSpaceMap F G).app (Opposite.op ⦋0⦌)
        (smallUnstraighteningHomParameter a) := by
  rw [smallUnstraighteningFunctorHom_vertex]
  exact congrArg (fun m => m.app (Opposite.op ⦋0⦌) (smallUnstraighteningHomParameter a))
    (liftedSmallLeftUnstraighteningMappingSpaceMap_comparison F G)

end SerrePositivity.KST.Fibration

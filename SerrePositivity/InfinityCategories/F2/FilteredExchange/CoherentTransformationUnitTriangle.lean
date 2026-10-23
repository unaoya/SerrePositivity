module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTransformationVertexTriangle
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentConstantRepresentationLarge

/-!
概要：元の coherent 変換と標的の指定単位を全三角形で合成する。
方針：三角形の全空間合成比較に、元の単位の指定表現同型を続ける。
規約：元の二辺と選択済み三角形を保持。使われ方：元の変換による余錐の表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)

/-- 概要：元の変換と標的の単位を結ぶ全三角形の型。
方針：指定二辺を元の変換と元の単位の表現に固定。
規約：長辺と三つの制限も保持。使われ方：同じ三角形での指定比較。 -/
abbrev CoherentTransformationUnitTriangle :=
  CoherentTransformationVertexTriangle F G (SSet.const (coherentDiagramTotalVertex G)) t
    (coherentTotalUnitRepresentation G).1

/-- 概要：元の変換と元の単位の合成三角形を全データ付きで選ぶ。
方針：二辺固定の三角形充填。規約：単位を選び直さない。使われ方：指定余錐の回収。 -/
def coherentTransformationUnitTriangle : CoherentTransformationUnitTriangle F G t :=
  coherentTransformationVertexTriangle F G (SSet.const (coherentDiagramTotalVertex G)) t
    (coherentTotalUnitRepresentation G).1

/-- 概要：元の合成三角形の長辺の全空間射は元の変換の作用と元の単位の合成に同型。
方針：指定三角形の全空間比較に元の単位の表現同型を前合成して続ける。
規約：任意の指定済み三角形の比較。使われ方：元の余錐の標準比較への移送。 -/
def coherentTransformationUnitTriangleLargeIso (T : CoherentTransformationUnitTriangle F G t) :
    FunctorIso
      ((leftUnstraighteningMappingVertexMap F (SSet.const (coherentDiagramTotalVertex G))
        T.diagonal).val ≫ constantUnstraighteningFiberProjection _ (coherentDiagramTotalVertex G) ≫
          (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom)
      ((leftUnstraighteningMappingVertexMap F G t).val ≫ coherentLargeTotalUnit G) := by
  have e := (unstraighteningTriangleVertexIso F G
    (SSet.const (coherentDiagramTotalVertex G)) t (coherentTotalUnitRepresentation G).1
    T.diagonal T.diagram T.first T.second T.long).postcomp
      (constantUnstraighteningFiberProjection _ (coherentDiagramTotalVertex G) ≫
        (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex G)).hom)
  have eu := CoherentConstantRepresentation.largeIso G (coherentDiagramTotalVertex G)
    (coherentDiagramTotalUnit G) (coherentTotalUnitRepresentation G)
  exact e ≪≫ eu.precomp (leftUnstraighteningMappingVertexMap F G t).val

end SerrePositivity.InfinityCategories.F2

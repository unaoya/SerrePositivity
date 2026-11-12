module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitNativeDiagonalRepresentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationUnitCocone

/-!
概要：元の単位正方形の対角を実現した余錐と a6 の指定 native 写像を比較する。
方針：同じ全空間作用と単位を表す二つの余錐を比較し、native 表示を続ける。
規約：元の対角と指定 native 写像を保持。使われ方：余極限関手の辺との全余錐比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の単位正方形の対角変換を実現した、元の図式上の指定余錐。 -/
def coherentColimitNativeDiagonalCocone : JoinCocone F :=
  coherentRepresentationCocone F (coherentDiagramTotalVertex G)
    (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H) ≫
      coherentDiagramTotalUnit G) (coherentColimitNativeDiagonalRepresentation B H)

/-- 対角余錐の頂点は元の標的の全空間頂点。 -/
lemma coherentColimitNativeDiagonalCocone_vertex :
    (coherentColimitNativeDiagonalCocone B H).vertex = coherentDiagramTotalVertex G :=
  coherentRepresentationCocone_vertex _ _ _ _

/-- a6 の元の指定 native 写像の余錐は、元の単位正方形の対角の余錐と同型。 -/
def coherentColimitNativeDiagonalCoconeIso :
    VertexIso (X := coconeMappingSpace F (coherentDiagramTotalVertex G))
      ((coconePointHomFamily (coherentDiagramTotalCocone F)
        (coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (coherentTotalMapNativeRepresentation F G
            (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))).1)
      (coconeMappingPointAt (coherentColimitNativeDiagonalCocone B H)
        (coherentDiagramTotalVertex G) (coherentColimitNativeDiagonalCocone_vertex B H)) :=
  (coherentTotalMapNativeRepresentation F G
    (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))).2 ≪≫
      coherentRepresentationCoconeIso F (coherentDiagramTotalVertex G)
        (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H) ≫
          coherentDiagramTotalUnit G)
        (coherentConstantRepresentation F (coherentDiagramTotalVertex G)
          (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H) ≫
            coherentDiagramTotalUnit G))
        (coherentColimitNativeDiagonalRepresentation B H)

end SerrePositivity.InfinityCategories.F2

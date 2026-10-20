module

public import SerrePositivity.InfinityCategories.F2.CoherentTransformationUnitRepresentation
public import SerrePositivity.InfinityCategories.F2.CoherentRepresentationCoconeComparison
public import SerrePositivity.InfinityCategories.F2.CoherentTotalMapNative

/-!
概要：元の変換と単位の合成三角形を native 余錐・余極限写像の表示へ接続する。
方針：元の長辺の表現から余錐を実現し、同じ全空間射の二表現を比較する。
規約：元の三角形を保持。使われ方：元の coherent 変換による余極限写像の照合。
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
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (t : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
  (T : CoherentTransformationUnitTriangle F G t)

/-- 概要：元の変換と指定単位の同じ三角形の長辺を実現した native 余錐。
方針：長辺の指定表現を実現。規約：元の三角形を保持。使われ方：写像余錐との照合。 -/
def coherentTransformationUnitCocone : JoinCocone F :=
  coherentRepresentationCocone F (coherentDiagramTotalVertex G)
    (coherentTransformationTotalMap F G t ≫ coherentDiagramTotalUnit G)
    (coherentTransformationUnitRepresentation F G t T)

/-- 概要：元の合成三角形の余錐の頂点は標的の元の余極限頂点。
方針：長辺の実現の頂点式。規約：厳密な等式。使われ方：余錐の比較点。 -/
lemma coherentTransformationUnitCocone_vertex :
    (coherentTransformationUnitCocone F G t T).vertex = coherentDiagramTotalVertex G :=
  coherentRepresentationCocone_vertex _ _ _ _

/-- 概要：元の三角形からの余錐は元の全空間写像からの指定余錐と同型。
方針：同じ指定射の二表現の標準比較の充満忠実性。
規約：元の二余錐・三角形を保持。使われ方：native 余極限写像の元の図式との整合。 -/
def coherentTransformationUnitCoconeIso :
    VertexIso (X := coconeMappingSpace F (coherentDiagramTotalVertex G))
      (coconeMappingPointAt (coherentTransformationUnitCocone F G t T)
        (coherentDiagramTotalVertex G) (coherentTransformationUnitCocone_vertex F G t T))
      (coconeMappingPointAt (coherentTotalMapCocone F G (coherentTransformationTotalMap F G t))
        (coherentDiagramTotalVertex G)
        (coherentTotalMapCocone_vertex F G (coherentTransformationTotalMap F G t))) :=
  coherentRepresentationCoconeIso F (coherentDiagramTotalVertex G)
    (coherentTransformationTotalMap F G t ≫ coherentDiagramTotalUnit G)
    (coherentTransformationUnitRepresentation F G t T)
    (coherentConstantRepresentation F (coherentDiagramTotalVertex G)
      (coherentTransformationTotalMap F G t ≫ coherentDiagramTotalUnit G))

/-- 概要：元の native 余極限写像が表す余錐は元の変換と単位の合成三角形の余錐に同型。
方針：元の native 写像の表示を、同じ全空間射を表す二余錐の比較へ続ける。
規約：選択済み native 写像と元の三角形を保持。使われ方：元の二射影の余極限写像。 -/
def coherentTransformationNativeCoconeIso :
    VertexIso (X := coconeMappingSpace F (coherentDiagramTotalVertex G))
      ((coconePointHomFamily (coherentDiagramTotalCocone F)
        (coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (coherentTotalMapNativeRepresentation F G (coherentTransformationTotalMap F G t)).1)
      (coconeMappingPointAt (coherentTransformationUnitCocone F G t T)
        (coherentDiagramTotalVertex G) (coherentTransformationUnitCocone_vertex F G t T)) :=
  (coherentTotalMapNativeRepresentation F G (coherentTransformationTotalMap F G t)).2 ≪≫
    (coherentTransformationUnitCoconeIso F G t T).symm

end SerrePositivity.InfinityCategories.F2

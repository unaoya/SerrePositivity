module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitNativeUnitTriangle
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentConstantTriangleRepresentation

/-!
概要：単位自然性の元の対角を、元の変換の全空間作用と単位の合成の表現にする。
方針：元の native 単位表現と同じ上二単体を、一般の指定表現の合成定理へ入力する。
規約：対角・単位・変換を保持。使われ方：a6 の native 写像との元の余錐の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の対角変換は、元の変換の小さい全空間作用と元の単位の合成を表す。 -/
def coherentColimitNativeDiagonalRepresentation : CoherentConstantRepresentation F
    (coherentDiagramTotalVertex G)
    (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H) ≫
      coherentDiagramTotalUnit G) :=
  coherentConstantTriangleRepresentation F G (coherentDiagramTotalVertex G)
    (coherentDiagramTotalUnit G) (coherentNativeUnitRepresentation G)
    (coherentVertexOfHomotopy H) (coherentColimitNativeUnitTriangle B H)

/-- 表現の第一成分は元の正方形の対角円柱そのものを表す。 -/
lemma coherentColimitNativeDiagonalRepresentation_vertex :
    (coherentColimitNativeDiagonalRepresentation B H).1 =
      coherentVertexOfHomotopy (coherentColimitNativeUnitDiagonal B H) := rfl

end SerrePositivity.InfinityCategories.F2

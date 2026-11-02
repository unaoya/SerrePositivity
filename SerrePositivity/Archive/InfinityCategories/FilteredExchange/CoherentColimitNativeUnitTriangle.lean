module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitTriangles
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeUnitRepresentation

/-!
概要：元の単位正方形の上三角形を、指定全空間頂点の native 単位表現に接続する。
方針：頂点の等式だけを型へ反映し、全三角形と元の対角円柱を保持する。
規約：余錐も単位も選び直さない。使われ方：native 余極限写像の元の単位整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)

/-- 元の単位正方形の対角を、元の指定全空間頂点を持つ同じ実円柱で読む。 -/
def coherentColimitNativeUnitDiagonal :
    SSet.Homotopy F (SSet.const (coherentDiagramTotalVertex G)) where
  h := (coherentColimitUnitDiagonal B H).h
  h₀ := (coherentColimitUnitDiagonal B H).h₀
  h₁ := by
    change SSet.ι₁ ≫ (coherentColimitUnitDiagonal B H).h =
      SSet.const (coherentDiagramTotalVertex G)
    exact (coherentColimitUnitDiagonal B H).h₁.trans
      (congrArg SSet.const (coherentDiagramTotalCocone_vertex G))
  rel := (coherentColimitUnitDiagonal B H).rel

/-- 元の上二単体を、指定された native 単位円柱を後辺に持つ三角形として読む。 -/
def coherentColimitNativeUnitFunctorTriangle : FunctorCompositionTriangle H
    (coherentNativeUnitHomotopy G) (coherentColimitNativeUnitDiagonal B H) where
  diagram := (coherentColimitUnitUpperTriangle B H).diagram
  face_zero := by
    rw [coherentNativeUnitHomotopy_h]
    exact (coherentColimitUnitUpperTriangle B H).face_zero
  face_one := (coherentColimitUnitUpperTriangle B H).face_one
  face_two := (coherentColimitUnitUpperTriangle B H).face_two

/-- 元の指定変換と native 単位表現を持つ、元の全上三角形の coherent 表示。 -/
def coherentColimitNativeUnitTriangle : CoherentTransformationVertexTriangle F G
    (SSet.const (coherentDiagramTotalVertex G)) (coherentVertexOfHomotopy H)
    (coherentNativeUnitRepresentation G).1 := by
  have T := coherentTriangleOfFunctorTriangle (coherentColimitNativeUnitFunctorTriangle B H)
  refine ⟨T.diagonal, T.diagram, T.first, ?_, T.long⟩
  simpa only [coherentNativeUnitHomotopy, coherentVertexOfHomotopy_of_vertex] using T.second

/-- 上三角形の長変換は、元の対角円柱を変更せずに表示したもの。 -/
lemma coherentColimitNativeUnitTriangle_diagonal :
    (coherentColimitNativeUnitTriangle B H).diagonal =
      coherentVertexOfHomotopy (coherentColimitNativeUnitDiagonal B H) := rfl

end SerrePositivity.InfinityCategories.F2

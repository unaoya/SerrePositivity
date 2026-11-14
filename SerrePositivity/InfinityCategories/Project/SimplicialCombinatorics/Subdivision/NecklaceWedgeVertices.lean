module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeFunctor
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceVertices

/-! # 連結した全 necklace 射の元の頂点作用
概要：wedge 射の左右への制限が、元の全頂点作用を厳密に回収する。
方針：元の単体的な包含の自然性を零単体で評価する。
規約：各辺や生成語での検証に限定しない。使われ方：具体的 cube tensor との比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 任意の連結射の左側の頂点作用は、元の左射の頂点作用と同じ番号の包含。 -/
lemma necklaceVertexMap_wedge_left {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U')
    (v : T.down.Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g) (T.down.wedgeLeftVertex U.down v) =
      T'.down.wedgeLeftVertex U'.down (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f v) := by
  have e := ConcreteCategory.congr_hom (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_inl f g) _)
    (T.down.vertexEquiv.symm v)
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T' U').down.vertexEquiv e

/-- 任意の連結射の右側の頂点作用は、元の右射の頂点作用と同じ番号移動。 -/
lemma necklaceVertexMap_wedge_right {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ T') (g : U ⟶ U')
    (v : U.down.Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g) (T.down.wedgeRightVertex U.down v) =
      T'.down.wedgeRightVertex U'.down (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap g v) := by
  have e := ConcreteCategory.congr_hom (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_inr f g) _)
    (U.down.vertexEquiv.symm v)
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T' U').down.vertexEquiv e

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceVertexMap_wedge_left := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceVertexMap_wedge_right := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_right

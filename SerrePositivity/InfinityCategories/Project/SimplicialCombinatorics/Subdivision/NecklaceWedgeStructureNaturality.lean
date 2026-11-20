module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceWedgeStructureVertices

/-! # 元の全 necklace 射に関する構造同型の自然性
概要：元の結合・左右単位の同型は、元の全端点保存単体的写像について自然となる。
方針：全頂点での射の判定と、元の三ブロック・一点単位の回収式を使う。
規約：射を生成語へ制限しない。使われ方：native wedge のモノイダル圏。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の結合同型は、元の任意の三つの necklace 射について自然。 -/
lemma necklaceAssociator_naturality {T T' U U' V V' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}}
    (f : T ⟶ T') (g : U ⟶ U') (h : V ⟶ V') :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f g) h ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T' U' V').hom =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T U V).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap g h) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_comp, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_comp]
  funext v
  rcases (T.down.wedge U.down).wedgeVertex_cases V.down v with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rcases T.down.wedgeVertex_cases U.down a with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ _) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ _)
      rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_left, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_left,
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_left, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_left,
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_left]
    · change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ _) =
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ _)
      rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_left, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_right,
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_middle, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_middle,
        _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_right, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_left]
  · change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ _) =
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ _)
    rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_right, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_right,
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_right, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_right, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_right]

/-- 元の左単位は、元の任意の necklace 射について自然。 -/
lemma necklaceLeftUnitor_naturality {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap (𝟙 _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint) f ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor U).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor T).hom ≫ f := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_comp, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_comp]
  funext v
  obtain ⟨a, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePointWedge_vertex_surjective T v
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ _) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ _)
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_right, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor_vertex_right,
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor_vertex_right]

/-- 元の右単位は、元の任意の necklace 射について自然。 -/
lemma necklaceRightUnitor_naturality {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap f (𝟙 _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint) ≫ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor U).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor T).hom ≫ f := by
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_comp, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_comp]
  funext v
  obtain ⟨a, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgePoint_vertex_surjective T v
  change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ _) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap _ _)
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_wedge_left, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor_vertex_left,
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor_vertex_left]

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

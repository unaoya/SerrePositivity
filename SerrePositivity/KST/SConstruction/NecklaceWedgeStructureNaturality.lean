module
public import SerrePositivity.KST.SConstruction.NecklaceWedgeStructureVertices

/-! # 元の全 necklace 射に関する構造同型の自然性
概要：元の結合・左右単位の同型は、元の全端点保存単体的写像について自然となる。
方針：全頂点での射の判定と、元の三ブロック・一点単位の回収式を使う。
規約：射を生成語へ制限しない。使われ方：native wedge のモノイダル圏。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の結合同型は、元の任意の三つの necklace 射について自然。 -/
lemma necklaceAssociator_naturality {T T' U U' V V' : Necklace.{u}}
    (f : T ⟶ T') (g : U ⟶ U') (h : V ⟶ V') :
    necklaceWedgeMap (necklaceWedgeMap f g) h ≫ (necklaceAssociator T' U' V').hom =
      (necklaceAssociator T U V).hom ≫ necklaceWedgeMap f (necklaceWedgeMap g h) := by
  apply necklaceVertexMap_injective
  rw [necklaceVertexMap_comp, necklaceVertexMap_comp]
  funext v
  rcases (T.down.wedge U.down).wedgeVertex_cases V.down v with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rcases T.down.wedgeVertex_cases U.down a with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · change necklaceVertexMap _ (necklaceVertexMap _ _) =
        necklaceVertexMap _ (necklaceVertexMap _ _)
      rw [necklaceVertexMap_wedge_left, necklaceVertexMap_wedge_left,
        necklaceAssociator_vertex_left, necklaceAssociator_vertex_left,
        necklaceVertexMap_wedge_left]
    · change necklaceVertexMap _ (necklaceVertexMap _ _) =
        necklaceVertexMap _ (necklaceVertexMap _ _)
      rw [necklaceVertexMap_wedge_left, necklaceVertexMap_wedge_right,
        necklaceAssociator_vertex_middle, necklaceAssociator_vertex_middle,
        necklaceVertexMap_wedge_right, necklaceVertexMap_wedge_left]
  · change necklaceVertexMap _ (necklaceVertexMap _ _) =
      necklaceVertexMap _ (necklaceVertexMap _ _)
    rw [necklaceVertexMap_wedge_right, necklaceAssociator_vertex_right,
      necklaceAssociator_vertex_right, necklaceVertexMap_wedge_right, necklaceVertexMap_wedge_right]

/-- 元の左単位は、元の任意の necklace 射について自然。 -/
lemma necklaceLeftUnitor_naturality {T U : Necklace.{u}} (f : T ⟶ U) :
    necklaceWedgeMap (𝟙 necklacePoint) f ≫ (necklaceLeftUnitor U).hom =
      (necklaceLeftUnitor T).hom ≫ f := by
  apply necklaceVertexMap_injective
  rw [necklaceVertexMap_comp, necklaceVertexMap_comp]
  funext v
  obtain ⟨a, rfl⟩ := necklacePointWedge_vertex_surjective T v
  change necklaceVertexMap _ (necklaceVertexMap _ _) = necklaceVertexMap _ (necklaceVertexMap _ _)
  rw [necklaceVertexMap_wedge_right, necklaceLeftUnitor_vertex_right,
    necklaceLeftUnitor_vertex_right]

/-- 元の右単位は、元の任意の necklace 射について自然。 -/
lemma necklaceRightUnitor_naturality {T U : Necklace.{u}} (f : T ⟶ U) :
    necklaceWedgeMap f (𝟙 necklacePoint) ≫ (necklaceRightUnitor U).hom =
      (necklaceRightUnitor T).hom ≫ f := by
  apply necklaceVertexMap_injective
  rw [necklaceVertexMap_comp, necklaceVertexMap_comp]
  funext v
  obtain ⟨a, rfl⟩ := necklaceWedgePoint_vertex_surjective T v
  change necklaceVertexMap _ (necklaceVertexMap _ _) = necklaceVertexMap _ (necklaceVertexMap _ _)
  rw [necklaceVertexMap_wedge_left, necklaceRightUnitor_vertex_left,
    necklaceRightUnitor_vertex_left]

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.NecklaceWedgeStructure
public import SerrePositivity.KST.SConstruction.NecklaceWedgeVertices
public import SerrePositivity.KST.SConstruction.NecklaceWedgeBooleanJoin

/-! # 元の wedge 構造同型の全頂点作用
概要：三つの元のブロックと一点単位で、構造同型が全頂点を保持することを示す。
方針：対象等号の全頂点番号の保存と、元の番号の和を照合する。
規約：元の全頂点を扱う。使われ方：全単体的射に関する結合・単位の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の結合同型は、元のすべての頂点番号を保つ。 -/
lemma necklaceAssociator_vertex_val (T U V : Necklace.{u})
    (v : (necklaceWedge (necklaceWedge T U) V).down.Vertex) :
    (necklaceVertexMap (necklaceAssociator T U V).hom v).val = v.val :=
  necklaceVertexMap_eqToHom_val.{u}
    (necklace_eq_of_shape (T.down.wedge_assoc U.down V.down)) v

/-- 元の結合同型は左ブロックを元の左包含で回収する。 -/
lemma necklaceAssociator_vertex_left (T U V : Necklace.{u}) (v : T.down.Vertex) :
    necklaceVertexMap (necklaceAssociator T U V).hom
        ((T.down.wedge U.down).wedgeLeftVertex V.down (T.down.wedgeLeftVertex U.down v)) =
      T.down.wedgeLeftVertex (U.down.wedge V.down) v :=
  Fin.ext (necklaceAssociator_vertex_val T U V _)

/-- 元の結合同型は中央ブロックを元の二つの包含で回収する。 -/
lemma necklaceAssociator_vertex_middle (T U V : Necklace.{u}) (v : U.down.Vertex) :
    necklaceVertexMap (necklaceAssociator T U V).hom
        ((T.down.wedge U.down).wedgeLeftVertex V.down (T.down.wedgeRightVertex U.down v)) =
      T.down.wedgeRightVertex (U.down.wedge V.down) (U.down.wedgeLeftVertex V.down v) :=
  Fin.ext (necklaceAssociator_vertex_val T U V _)

/-- 元の結合同型は右ブロックを元の二つの右包含で回収する。 -/
lemma necklaceAssociator_vertex_right (T U V : Necklace.{u}) (v : V.down.Vertex) :
    necklaceVertexMap (necklaceAssociator T U V).hom
        ((T.down.wedge U.down).wedgeRightVertex V.down v) =
      T.down.wedgeRightVertex (U.down.wedge V.down) (U.down.wedgeRightVertex V.down v) := by
  apply Fin.ext
  have h := necklaceAssociator_vertex_val T U V
    ((T.down.wedge U.down).wedgeRightVertex V.down v)
  change _ = T.down.vertexMax + (U.down.vertexMax + v.val)
  change _ = T.down.vertexMax + U.down.vertexMax + v.val at h
  omega

/-- 元の左単位は、元の右包含からすべての頂点を回収する。 -/
lemma necklaceLeftUnitor_vertex_right (T : Necklace.{u}) (v : T.down.Vertex) :
    necklaceVertexMap (necklaceLeftUnitor T).hom
      (necklacePoint.down.wedgeRightVertex T.down v) = v := by
  have h : (necklaceVertexMap (necklaceLeftUnitor T).hom
      (necklacePoint.down.wedgeRightVertex T.down v)).val = 0 + v.val :=
    necklaceVertexMap_eqToHom_val.{u}
      (necklace_eq_of_shape (T := necklaceWedge necklacePoint T) (U := T)
        T.down.single_zero_wedge) _
  exact Fin.ext (h.trans (Nat.zero_add v.val))

/-- 元の右単位は、元の左包含からすべての頂点を回収する。 -/
lemma necklaceRightUnitor_vertex_left (T : Necklace.{u}) (v : T.down.Vertex) :
    necklaceVertexMap (necklaceRightUnitor T).hom (T.down.wedgeLeftVertex necklacePoint.down v) =
      v := Fin.ext (necklaceVertexMap_eqToHom_val.{u}
        (necklace_eq_of_shape (T := necklaceWedge T necklacePoint) (U := T)
          T.down.wedge_single_zero) _)

/-- 左に一点を貼った全頂点は、元の右 necklace から来る。 -/
lemma necklacePointWedge_vertex_surjective (T : Necklace.{u}) :
    Function.Surjective (necklacePoint.down.wedgeRightVertex T.down) := by
  intro v
  have h := v.isLt
  change v.val < 0 + T.down.vertexMax + 1 at h
  exact ⟨⟨v.val, by omega⟩, Fin.ext (by change 0 + v.val = v.val; omega)⟩

/-- 右に一点を貼った全頂点は、元の左 necklace から来る。 -/
lemma necklaceWedgePoint_vertex_surjective (T : Necklace.{u}) :
    Function.Surjective (T.down.wedgeLeftVertex necklacePoint.down) := by
  intro v
  have h := v.isLt
  change v.val < T.down.vertexMax + 0 + 1 at h
  exact ⟨⟨v.val, by omega⟩, Fin.ext rfl⟩

end SerrePositivity.KST.SConstruction

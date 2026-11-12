module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceWedgeStructure
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceWedgeVertices
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceWedgeBooleanJoin

/-! # 元の wedge 構造同型の全頂点作用
概要：三つの元のブロックと一点単位で、構造同型が全頂点を保持することを示す。
方針：対象等号の全頂点番号の保存と、元の番号の和を照合する。
規約：元の全頂点を扱う。使われ方：全単体的射に関する結合・単位の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の結合同型は、元のすべての頂点番号を保つ。 -/
lemma necklaceAssociator_vertex_val (T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u})
    (v : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T U) V).down.Vertex) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T U V).hom v).val = v.val :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_eqToHom_val.{u}
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape (T.down.wedge_assoc U.down V.down)) v

/-- 元の結合同型は左ブロックを元の左包含で回収する。 -/
lemma necklaceAssociator_vertex_left (T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (v : T.down.Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T U V).hom
        ((T.down.wedge U.down).wedgeLeftVertex V.down (T.down.wedgeLeftVertex U.down v)) =
      T.down.wedgeLeftVertex (U.down.wedge V.down) v :=
  Fin.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_val T U V _)

/-- 元の結合同型は中央ブロックを元の二つの包含で回収する。 -/
lemma necklaceAssociator_vertex_middle (T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (v : U.down.Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T U V).hom
        ((T.down.wedge U.down).wedgeLeftVertex V.down (T.down.wedgeRightVertex U.down v)) =
      T.down.wedgeRightVertex (U.down.wedge V.down) (U.down.wedgeLeftVertex V.down v) :=
  Fin.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_val T U V _)

/-- 元の結合同型は右ブロックを元の二つの右包含で回収する。 -/
lemma necklaceAssociator_vertex_right (T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (v : V.down.Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator T U V).hom
        ((T.down.wedge U.down).wedgeRightVertex V.down v) =
      T.down.wedgeRightVertex (U.down.wedge V.down) (U.down.wedgeRightVertex V.down v) := by
  apply Fin.ext
  have h := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_val T U V
    ((T.down.wedge U.down).wedgeRightVertex V.down v)
  change _ = T.down.vertexMax + (U.down.vertexMax + v.val)
  change _ = T.down.vertexMax + U.down.vertexMax + v.val at h
  omega

/-- 元の左単位は、元の右包含からすべての頂点を回収する。 -/
lemma necklaceLeftUnitor_vertex_right (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (v : T.down.Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor T).hom
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down.wedgeRightVertex T.down v) = v := by
  have h : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor T).hom
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down.wedgeRightVertex T.down v)).val = 0 + v.val :=
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_eqToHom_val.{u}
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape (T := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint T) (U := T)
        T.down.single_zero_wedge) _
  exact Fin.ext (h.trans (Nat.zero_add v.val))

/-- 元の右単位は、元の左包含からすべての頂点を回収する。 -/
lemma necklaceRightUnitor_vertex_left (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) (v : T.down.Vertex) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor T).hom (T.down.wedgeLeftVertex _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down v) =
      v := Fin.ext (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_eqToHom_val.{u}
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape (T := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint) (U := T)
          T.down.wedge_single_zero) _)

/-- 左に一点を貼った全頂点は、元の右 necklace から来る。 -/
lemma necklacePointWedge_vertex_surjective (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down.wedgeRightVertex T.down) := by
  intro v
  have h := v.isLt
  change v.val < 0 + T.down.vertexMax + 1 at h
  exact ⟨⟨v.val, by omega⟩, Fin.ext (by change 0 + v.val = v.val; omega)⟩

/-- 右に一点を貼った全頂点は、元の左 necklace から来る。 -/
lemma necklaceWedgePoint_vertex_surjective (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    Function.Surjective (T.down.wedgeLeftVertex _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint.down) := by
  intro v
  have h := v.isLt
  change v.val < T.down.vertexMax + 0 + 1 at h
  exact ⟨⟨v.val, by omega⟩, Fin.ext rfl⟩

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceAssociator_vertex_left := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceAssociator_vertex_middle := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_middle

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceAssociator_vertex_right := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceAssociator_vertex_val := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator_vertex_val

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceLeftUnitor_vertex_right := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor_vertex_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklacePointWedge_vertex_surjective := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePointWedge_vertex_surjective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceRightUnitor_vertex_left := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor_vertex_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgePoint_vertex_surjective := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgePoint_vertex_surjective

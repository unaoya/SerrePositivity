module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceWedgeFunctor
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShapeEquality
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceVertices

/-! # 元の necklace の wedge の構造同型
概要：一点単位と、元の全頂点番号を保つ結合・左右単位の同型を構成する。
方針：有限 joints の元の等号を necklace 対象の等号へ移す。
規約：元の全単体的写像を使う。使われ方：native wedge のモノイダル構造。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の一点 necklace。 -/
def necklacePoint : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u} := ⟨_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single 0⟩

/-- 元の有限 joints の等号は、宇宙を固定した necklace 対象の等号を与える。 -/
lemma necklace_eq_of_shape {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (h : T.down = U.down) : T = U := ULift.ext h

/-- 元の wedge の結合同型。 -/
def necklaceAssociator (T U V : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T U) V ≅ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge U V) :=
  eqToIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape (T.down.wedge_assoc U.down V.down))

/-- 元の一点を左単位とする同型。 -/
def necklaceLeftUnitor (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint T ≅ T :=
  eqToIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape (T.down.single_zero_wedge))

/-- 元の一点を右単位とする同型。 -/
def necklaceRightUnitor (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge T _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint ≅ T :=
  eqToIso (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape (T.down.wedge_single_zero))

/-- 対象等号による元の necklace 射は、元の全頂点番号を保持する。 -/
lemma necklaceVertexMap_eqToHom_val {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (h : T = U) (v : T.down.Vertex) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap (eqToHom h) v).val = v.val := by
  cases h
  exact congrArg Fin.val (congrFun (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_id T) v)

/-- 元の wedge 射は、両側の対象等号による移送を保持する。 -/
lemma necklaceWedgeMap_eqToHom {T T' U U' : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (h : T = T') (k : U = U') :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap (eqToHom h) (eqToHom k) = eqToHom (congrArg₂ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedge h k) := by
  cases h
  cases k
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_id T U

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceAssociator := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceLeftUnitor := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklacePoint := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklacePoint

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceRightUnitor := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceVertexMap_eqToHom_val := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_eqToHom_val

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceWedgeMap_eqToHom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceWedgeMap_eqToHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklace_eq_of_shape := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklace_eq_of_shape

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceAssociator._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceAssociator._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceLeftUnitor._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceLeftUnitor._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceRightUnitor._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceRightUnitor._proof_1

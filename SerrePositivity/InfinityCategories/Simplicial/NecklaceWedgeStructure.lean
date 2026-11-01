module
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceWedgeFunctor
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceShapeEquality
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceVertices

/-! # 元の necklace の wedge の構造同型
概要：一点単位と、元の全頂点番号を保つ結合・左右単位の同型を構成する。
方針：有限 joints の元の等号を necklace 対象の等号へ移す。
規約：元の全単体的写像を使う。使われ方：native wedge のモノイダル構造。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の一点 necklace。 -/
def necklacePoint : Necklace.{u} := ⟨NecklaceShape.single 0⟩

/-- 元の有限 joints の等号は、宇宙を固定した necklace 対象の等号を与える。 -/
lemma necklace_eq_of_shape {T U : Necklace.{u}} (h : T.down = U.down) : T = U := ULift.ext h

/-- 元の wedge の結合同型。 -/
def necklaceAssociator (T U V : Necklace.{u}) :
    necklaceWedge (necklaceWedge T U) V ≅ necklaceWedge T (necklaceWedge U V) :=
  eqToIso (necklace_eq_of_shape (T.down.wedge_assoc U.down V.down))

/-- 元の一点を左単位とする同型。 -/
def necklaceLeftUnitor (T : Necklace.{u}) : necklaceWedge necklacePoint T ≅ T :=
  eqToIso (necklace_eq_of_shape (T.down.single_zero_wedge))

/-- 元の一点を右単位とする同型。 -/
def necklaceRightUnitor (T : Necklace.{u}) : necklaceWedge T necklacePoint ≅ T :=
  eqToIso (necklace_eq_of_shape (T.down.wedge_single_zero))

/-- 対象等号による元の necklace 射は、元の全頂点番号を保持する。 -/
lemma necklaceVertexMap_eqToHom_val {T U : Necklace.{u}} (h : T = U) (v : T.down.Vertex) :
    (necklaceVertexMap (eqToHom h) v).val = v.val := by
  cases h
  exact congrArg Fin.val (congrFun (necklaceVertexMap_id T) v)

/-- 元の wedge 射は、両側の対象等号による移送を保持する。 -/
lemma necklaceWedgeMap_eqToHom {T T' U U' : Necklace.{u}} (h : T = T') (k : U = U') :
    necklaceWedgeMap (eqToHom h) (eqToHom k) = eqToHom (congrArg₂ necklaceWedge h k) := by
  cases h
  cases k
  exact necklaceWedgeMap_id T U

end SerrePositivity.KST.SConstruction

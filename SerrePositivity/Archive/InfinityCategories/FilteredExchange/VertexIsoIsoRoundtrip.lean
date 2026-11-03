module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleTotalComponent

/-!
概要：単体集合の同型で写した指定頂点同型を逆で戻すと、元の値に戻る。
方針：ホモトピー圏の合成則と恒等写像での値の回収を使う。
規約：指定同型を保持。使われ方：内部 Hom の縮小と復元の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ指定同型を同型とその逆で写す往復は、元の指定値を保持する。 -/
lemma vertexIso_map_iso_roundtrip {X Y : SSet.{u}} (i : X ≅ Y)
    {x y : X _⦋0⦌} (e : VertexIso x y) :
    HEq (VertexIso.map (VertexIso.map e i.hom) i.inv) e :=
  (heq_of_eq (vertexIso_map_comp e i.hom i.inv)).trans
    ((vertexIso_map_heq e i.hom_inv_id).trans (vertexIso_map_identity_heq e))

end SerrePositivity.InfinityCategories.F2

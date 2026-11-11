module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LiftEndpoint

/-!
概要：可縮な選択空間の指定同型は任意の制限先の可縮な空間で同じ指定同型となる。
方針：制限先のホモトピー圏の終対象への射の一意性を使う。
規約：指定同型の値の等式。使われ方：全空間と各点の持ち上げの比較の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：可縮な空間への指定同型の像はその空間の標準頂点同型に等しい。
方針：標的頂点の終対象性による射の一意性。
規約：指定同型の等式。使われ方：持ち上げの比較の選択を制限先で照合。 -/
lemma vertexIso_map_eq_contractible {K L : SSet.{u}} (hL : IsContractibleKan L)
    {x y : K _⦋0⦌} (e : VertexIso x y) (f : K ⟶ L) :
    VertexIso.map e f = hL.vertexIso (f.app (Opposite.op ⦋0⦌) x)
      (f.app (Opposite.op ⦋0⦌) y) := by
  have := hL.kanComplex
  apply Iso.ext
  exact (hL.isTerminalVertex (f.app (Opposite.op ⦋0⦌) y)).isTerminalHo.hom_ext _ _

/-- 概要：二つの可縮な選択空間の標準頂点同型は任意の写像に自然。
方針：制限先での指定同型の一意性。
規約：指定値の等式。使われ方：全空間の比較を各点の比較へ移す。 -/
lemma contractibleVertexIso_map {K L : SSet.{u}} (hK : IsContractibleKan K)
    (hL : IsContractibleKan L) (f : K ⟶ L) (x y : K _⦋0⦌) :
    VertexIso.map (hK.vertexIso x y) f =
      hL.vertexIso (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) :=
  vertexIso_map_eq_contractible hL _ f

end SerrePositivity.InfinityCategories.F2

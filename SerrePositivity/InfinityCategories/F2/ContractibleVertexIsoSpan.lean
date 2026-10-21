module

public import SerrePositivity.InfinityCategories.F2.ContractibleVertexIsoNaturality

/-!
概要：可縮な選択空間の二つの比較を合成した指定値は、共通の比較元に依存しない。
方針：ホモトピー圏の終対象への射の一意性と関手性を使う。
規約：指定同型の等式。使われ方：普遍 prism からの比較を共通の全錐からの比較へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 比較元を変えても、同じ二つの実延長間の指定同型の合成値は変わらない。 -/
lemma contractibleVertexIso_span {K : SSet.{u}} (hK : IsContractibleKan K)
    (x y z t : K _⦋0⦌) :
    (hK.vertexIso x z).symm ≪≫ hK.vertexIso x t =
      (hK.vertexIso y z).symm ≪≫ hK.vertexIso y t := by
  have := hK.kanComplex
  apply Iso.ext
  exact (hK.isTerminalVertex t).isTerminalHo.hom_ext _ _

/-- 任意の写像で終点や fiber の空間へ写した後も、同じ比較元変更の等式を保つ。 -/
lemma contractibleVertexIso_span_map {K L : SSet.{u}} (hK : IsContractibleKan K)
    (f : K ⟶ L) (x y z t : K _⦋0⦌) :
    (VertexIso.map (hK.vertexIso x z) f).symm ≪≫ VertexIso.map (hK.vertexIso x t) f =
      (VertexIso.map (hK.vertexIso y z) f).symm ≪≫ VertexIso.map (hK.vertexIso y t) f := by
  have h := congrArg (fun e => VertexIso.map e f) (contractibleVertexIso_span hK x y z t)
  simpa only [VertexIso.map, Functor.mapIso_trans, Functor.mapIso_symm] using h

end SerrePositivity.InfinityCategories.F2

module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.ContractibleVertexIsoNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence

/-!
概要：可縮な延長空間の選択済み比較を、合成と頂点の厳密な表示変更に整合させる。
方針：同じホモトピー圏の終対象への射の一意性と、元の関手の mapIso を使う。
規約：比較を選び直さない。使われ方：単位三単体の共有面の比較の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 可縮な空間で選択済みの二比較の合成は、同じ選択済み直接比較に等しい。 -/
lemma contractibleVertexIso_trans {K : SSet.{u}} (h : IsContractibleKan K)
    (x y z : K _⦋0⦌) : h.vertexIso x y ≪≫ h.vertexIso y z = h.vertexIso x z := by
  have := h.kanComplex
  apply Iso.ext
  exact (h.isTerminalVertex z).isTerminalHo.hom_ext _ _

/-- 同じ終点評価へ写した選択済み三比較も、同じ直接比較へ合成する。 -/
lemma contractibleVertexIso_map_trans {K L : SSet.{u}} (h : IsContractibleKan K)
    (x y z : K _⦋0⦌) (f : K ⟶ L) :
    VertexIso.map (h.vertexIso x y) f ≪≫ VertexIso.map (h.vertexIso y z) f =
      VertexIso.map (h.vertexIso x z) f := by
  rw [← vertexIso_map_trans, contractibleVertexIso_trans]

/-- 同じ中間頂点の表示変更を挟む二つの指定比較の合成から、その表示変更を消去。 -/
lemma transportedVertexIso_trans {C : Type u} [Category.{v} C]
    {x y z x' y' z' : C} (a : x ≅ x') (b : y ≅ y') (c : z ≅ z')
    (e : x ≅ y) (d : y ≅ z) :
    (a.symm ≪≫ e ≪≫ b) ≪≫ (b.symm ≪≫ d ≪≫ c) =
      a.symm ≪≫ (e ≪≫ d) ≪≫ c := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.F2

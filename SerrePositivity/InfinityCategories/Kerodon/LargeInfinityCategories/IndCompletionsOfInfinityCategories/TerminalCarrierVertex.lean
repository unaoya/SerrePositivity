module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalCarrierFiller
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalFaceIdentities

/-!
概要：鎖を実現する空間の零単体の値は、同じ添字に指定した元の頂点。
方針：零単体の条件を評価し、境界の最後の頂点を標準単体の最後の頂点と照合する。
規約：頂点は同型で置き換えず、厳密な等式で保持する。
使われ方：最後の部分複体の終頂点を使う境界充填。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Preorder I] {X : SSet.{u}}

/-- 同じ零単体の値は同じ添字に指定した頂点。 -/
lemma terminalCarrierValue_vertex {A : I → X.Subcomplex} {z : I → X _⦋0⦌}
    (g : (Δ[0] : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).toSSet) :
    g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue A z =
      SSet.yonedaEquiv.symm (z ((SSet.yonedaEquiv (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A z)).obj 0)) := by
  let e := SSet.yonedaEquiv g
  have he := e.property.2 (0 : Fin 1)
  have hid : SimplexCategory.const ⦋0⦌ ⦋0⦌ (0 : Fin 1) = 𝟙 ⦋0⦌ :=
    Subsingleton.elim _ _
  rw [hid] at he
  change X.map (𝟙 _) e.val.1 = z (e.val.2.obj 0) at he
  rw [CategoryTheory.Functor.map_id_apply] at he
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
  exact he

/-- 境界の最後の頂点を元の標準単体に含めると、最後の頂点写像になる。 -/
lemma boundaryLastVertex_ι (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex.{u} n (Fin.last (n + 1)) ≫ (boundary (n + 1)).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.lastVertexMap (n + 1) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.lastVertexMap, SSet.yonedaEquiv_map]
  rfl

/-- 元の鎖を最後の頂点で評価すると、元の最後の添字を得る。 -/
lemma nerveHom_lastVertex {n : ℕ} (q : (Δ[n] : SSet.{u}) ⟶ nerve I) :
    (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.lastVertexMap n ≫ q)).obj 0 =
      (SSet.yonedaEquiv q).obj (Fin.last n) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.lastVertexMap, ← SSet.yonedaEquiv_naturality]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

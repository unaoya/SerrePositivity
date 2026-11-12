module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices

/-!
概要：全部分複体内の両端を持つ元の実辺を、そのまま全部分複体へ戻す。
方針：区間の二頂点の条件で元の一単体の所属を確認する。
規約：元の辺そのものを保持し、可逆性や充填を仮定しない。
使われ方：compact 始域 slice 内での余錐頂点の延長。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：全部分複体の二頂点間の元の実辺を持ち上げる。
方針：元の一単体に両端の所属条件を付ける。
規約：辺の値を変更しない。
使われ方：compact 性を保った指定辺の同じ coslice への移送。 -/
def fullSubcomplexEdgeLift {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌)
    (e : X.Edge v.val w.val) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}).Edge v w := by
  have hmem : e.edge ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).obj (Opposite.op ⦋1⦌) := by
    intro a
    by_cases h : a.toOrderHom 0 = 0
    · have ha : a = SimplexCategory.δ (1 : Fin 2) := by
        apply SimplexCategory.Hom.ext
        apply DFunLike.ext
        intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        exact h
      rw [ha]
      exact (congrArg P e.src_eq).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v)
    · have h' : a.toOrderHom 0 = (1 : Fin 2) := by
        have hlt : (a.toOrderHom 0).val < 2 := (a.toOrderHom 0).isLt
        have hz : (a.toOrderHom 0).val ≠ 0 := fun hz ↦ h (Fin.ext hz)
        apply Fin.ext
        change (a.toOrderHom 0).val = 1
        omega
      have ha : a = SimplexCategory.δ (0 : Fin 2) := by
        apply SimplexCategory.Hom.ext
        apply DFunLike.ext
        intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        exact h'
      rw [ha]
      exact (congrArg P e.tgt_eq).mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex w)
  exact ⟨⟨e.edge, hmem⟩, Subtype.ext e.src_eq, Subtype.ext e.tgt_eq⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

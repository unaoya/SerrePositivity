module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalCarrierProjection

/-!
概要：終頂点付き部分複体の包含順の nerve を元の単体集合内に実現する。
方針：全鎖の実現空間の trivial Kan 射影の切断から同じ値写像を取り出す。
規約：各指定頂点と各鎖の最後の部分複体への所属を厳密に保持する。
使われ方：小さい終頂点付き部分複体の poset からの cofinal map の構成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Preorder I] {X : SSet.{u}}
  (A : I → X.Subcomplex) (hA : Monotone A)
  (t : ∀ i, (A i).toSSet _⦋0⦌) (ht : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (t i))

/-- 元の鎖の全ての面の条件を満たす、同じ射影の切断。 -/
def terminalCarrierSectionData :
    {s : nerve I ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A (fun i => (t i).val)).toSSet //
      s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A (fun i => (t i).val) = 𝟙 _} := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection_trivialKanFibration A hA t ht
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A (fun i => (t i).val))
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- 元の終頂点の割当てを保つ全鎖の整合的な実現。 -/
def terminalCarrierRealization : nerve I ⟶ X :=
  (terminalCarrierSectionData A hA t ht).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue A (fun i => (t i).val)

/-- 元の同じ零単体の値は指定した同じ頂点。 -/
lemma terminalCarrierRealization_vertex (g : (Δ[0] : SSet.{u}) ⟶ nerve I) :
    g ≫ terminalCarrierRealization A hA t ht =
      SSet.yonedaEquiv.symm (t ((SSet.yonedaEquiv g).obj 0)).val := by
  let s := terminalCarrierSectionData A hA t ht
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue_vertex (g ≫ s.val)
  have he : (g ≫ s.val) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A (fun i => (t i).val) = g := by
    rw [Category.assoc, s.property, Category.comp_id]
  rw [he] at h
  exact h

/-- 同じ鎖全体の値は、その最後の添字の元の部分複体に含まれる。 -/
lemma terminalCarrierRealization_range_le {n : ℕ} (q : (Δ[n] : SSet.{u}) ⟶ nerve I) :
    Subcomplex.range (q ≫ terminalCarrierRealization A hA t ht) ≤
      A ((SSet.yonedaEquiv q).obj (Fin.last n)) := by
  let s := terminalCarrierSectionData A hA t ht
  have he : (q ≫ s.val) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierProjection A (fun i => (t i).val) = (𝟙 _) ≫ q := by
    rw [Category.assoc, s.property, Category.comp_id, Category.id_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrierValue_range_le hA (q ≫ s.val) (𝟙 _) q he

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

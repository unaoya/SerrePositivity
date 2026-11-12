module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConeSimplexCases
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.TerminalCarrier

/-!
概要：右錐の新しい単体の最後の添字と、元の実現空間の頂点の値を照合する。
方針：最後の頂点への制限と元の写像の自然性を使う。
規約：同じ右頂点と指定した添字を厳密に保持する。
使われ方：元の図式と新しい余錐を実現空間内に貼り合わせる。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Preorder I] {X K : SSet.{u}}

/-- 最後の頂点が右頂点なら、同じ写像の最後の添字はその右頂点の添字。 -/
lemma coneMap_last_index (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ⟶ nerve I) (i : I)
    (hq : q.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex K) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i) {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u})) _⦋n⦌)
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplexVertex s (Fin.last n) = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneApex K) :
    (q.app _ s).obj (Fin.last n) = i := by
  have hn := ConcreteCategory.congr_hom
    (q.naturality (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op) s
  change q.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplexVertex s (Fin.last n)) =
    (nerve I).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)).op (q.app _ s) at hn
  have hh := congrArg (fun v : (nerve I) _⦋0⦌ => v.obj 0) hn
  change (q.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coneSimplexVertex s (Fin.last n))).obj 0 = (q.app _ s).obj (Fin.last n) at hh
  rw [hs, hq] at hh
  exact hh.symm

/-- 同じ実現空間の零単体の値は、その元の添字に指定した頂点。 -/
lemma terminalCarrier_vertex_value {A : I → X.Subcomplex} {z : I → X _⦋0⦌}
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.terminalCarrier A z).toSSet _⦋0⦌) : e.val.1 = z (e.val.2.obj 0) := by
  have he := e.property.2 (0 : Fin 1)
  rw [SimplexCategory.hom_zero_zero (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0)] at he
  change X.map (𝟙 _) e.val.1 = z (e.val.2.obj 0) at he
  rw [CategoryTheory.Functor.map_id_apply] at he
  exact he

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

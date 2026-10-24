module

public import SerrePositivity.InfinityCategories.F2.Ind.NerveSublevelLift

/-!
概要：頂点の共通上界を、同じ nerve 図式の余錐の頂点として実現する。
方針：下区間の最大対象の終対象性を使い、元の包含関手で戻す。
規約：余錐の頂点は指定した元の上界と厳密に一致する。
使われ方：有限 coslice 図式の添字を共通の部分複体まで延ばす。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Preorder I] {K : SSet.{u}}

/-- 全頂点の元の上界を厳密な頂点とする余錐が存在する。 -/
lemma exists_nerve_joinCocone_at_bound (a : K ⟶ nerve I) (i : I)
    (ha : ∀ v : K _⦋0⦌, (a.app _ v).obj 0 ≤ i) :
    ∃ c : JoinCocone a, c.vertex = nerveVertex i := by
  have ht : IsTerminalVertex (nerveVertex (⊤ : Set.Iic i)) :=
    SerrePositivity.InfinityCategories.F1B.nerveVertex_isTerminal isTerminalTop
  obtain ⟨c, hc⟩ := exists_joinCocone_at_terminal ht (nerveSublevelLift a i ha)
  let d : JoinCocone a := ⟨c.val ≫ nerveMap (sublevelInclusion i), by
    rw [← Category.assoc, c.property, nerveSublevelLift_inclusion]⟩
  refine ⟨d, ?_⟩
  rw [JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (joinInr K Δ[0] ≫ (c.val ≫ nerveMap (sublevelInclusion i))) = _
  rw [← Category.assoc, SSet.yonedaEquiv_comp, ← JoinCocone.vertex_eq, hc]
  rfl

end SerrePositivity.InfinityCategories.F2.Ind

module
public import SerrePositivity.InfinityCategories.Core.Cocone

public import SerrePositivity.InfinityCategories.Core.CoconeTransportPrism

/-!
概要：図式全体の前向き円柱の終端に余錐があれば、始端の元の図式にも余錐がある。
方針：終端の余錐を頂点固定の全円柱へ延長し、始端を制限する。
規約：円柱の可逆性を要求しない。使われ方：coslice 比較の一段への輸送から元の余錐へ戻る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 前向き円柱の終端の余錐から、元の始端図式の同じ頂点を持つ余錐を得る。 -/
lemma nonempty_joinCocone_of_prism {K X : SSet.{u}} [Quasicategory X]
    (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ X) {a b : K ⟶ X}
    (h₀ : prismEndpoint 0 K ≫ H = a) (h₁ : prismEndpoint 1 K ≫ H = b)
    (c : JoinCocone b) : Nonempty (JoinCocone a) := by
  obtain ⟨L, _, hLK, _⟩ := exists_cocone_fixedVertex_prism c.val H (h₁.trans c.property.symm)
  refine ⟨⟨prismEndpoint 0 _ ≫ L, ?_⟩⟩
  rw [← Category.assoc, ← prismEndpoint_naturality, Category.assoc, hLK, h₀]

end SerrePositivity.InfinityCategories.F2.Ind

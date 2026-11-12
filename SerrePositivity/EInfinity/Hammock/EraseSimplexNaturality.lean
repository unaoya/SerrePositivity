module

public import SerrePositivity.EInfinity.Hammock.EraseSimplex

/-!
# 元の恒等列の削除と全単体的作用素の整合

概要：元の一列の削除は、全ての face・degeneracy と厳密に交換する。
方針：同じ行の恒等列の条件を移し、元の包含とその単射性を使う。
規約：各次数での選択の違いは、元の射列の一意性で除く。
使われ方：基本縮約と縮約済みの代表の単体的作用素。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (j : Fin w.length) {n m : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).obj n) (hτ : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj k) j)
include hτ

lemma identityColumn_map (α : n ⟶ m) :
    ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).map α τ).obj k) j := by
  intro k
  exact hτ (α.unop.toOrderHom k)

/-- 元の削除の全作用素に対する厳密な自然性。 -/
lemma eraseSimplex_map (α : n ⟶ m) :
    eraseSimplex W X Y j ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).map α τ) (identityColumn_map W X Y j τ hτ α) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase w j) X Y).map α (eraseSimplex W X Y j τ hτ) := by
  apply graphDiagram_map_app_injective W _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective w j) X Y m
  rw [eraseSimplex_fac]
  have he := NatTrans.naturality_apply ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w j)) α
    (eraseSimplex W X Y j τ hτ)
  rw [eraseSimplex_fac] at he
  exact he.symm

end SerrePositivity.EInfinity.Hammock

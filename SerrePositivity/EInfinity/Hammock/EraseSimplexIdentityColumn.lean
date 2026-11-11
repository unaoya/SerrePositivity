module

public import SerrePositivity.EInfinity.Hammock.EraseSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumnEmbedding

/-!
# 元の恒等列を削除した後の他の恒等列の保存

概要：一つの恒等列を削除しても、残る位置の元の恒等列は恒等列のまま。
方針：同じ包含後の全射列の回収と、像の列での恒等性の反映を使う。
規約：元の全行での対象と射の等式。
使われ方：削除同士の局所合流。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

lemma eraseSimplex_identityColumn {C : Type u} [Category.{v} C] (W : MorphismProperty C)
    [W.IsMultiplicative] (X Y : C) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (j : Fin w.length) {n : SimplexCategoryᵒᵖ}
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).obj n) (hτ : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj k) j)
    (i : Fin (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase w j).length)
    (hi : ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj k) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w j).orderHom i)) :
    ∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn ((eraseSimplex W X Y j τ hτ).obj k) i := by
  intro k
  have he := congrArg (fun σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).obj n => σ.obj k) (eraseSimplex_fac W X Y j τ hτ)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w j) ((eraseSimplex W X Y j τ hτ).obj k) =
    τ.obj k at he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.identityColumn_obj_image_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion w j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_injective w j) _ i).mp
  rw [he]
  exact hi k

end SerrePositivity.EInfinity.Hammock

module

public import SerrePositivity.EInfinity.Hammock.EraseSimplex
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.IdentityColumnEmbedding

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
    [W.IsMultiplicative] (X Y : C) {w : Word} (j : Fin w.length) {n : SimplexCategoryᵒᵖ}
    (τ : (graph W w X Y).obj n) (hτ : ∀ k, IdentityColumn (τ.obj k) j)
    (i : Fin (Word.erase w j).length)
    (hi : ∀ k, IdentityColumn (τ.obj k) ((Word.eraseInclusion w j).orderHom i)) :
    ∀ k, IdentityColumn ((eraseSimplex W X Y j τ hτ).obj k) i := by
  intro k
  have he := congrArg (fun σ : (graph W w X Y).obj n => σ.obj k) (eraseSimplex_fac W X Y j τ hτ)
  change WordAction.obj (Word.eraseInclusion w j) ((eraseSimplex W X Y j τ hτ).obj k) =
    τ.obj k at he
  apply (identityColumn_obj_image_iff (Word.eraseInclusion w j)
    (Word.eraseInclusion_injective w j) _ i).mp
  rw [he]
  exact hi k

end SerrePositivity.EInfinity.Hammock

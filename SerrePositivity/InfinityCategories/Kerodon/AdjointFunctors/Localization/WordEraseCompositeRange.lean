module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordErasure
public import Mathlib.Data.Set.Lattice.Image

/-!
# 元の包含後に一列を削除した列の像

概要：部分語から一列を削除して元の語へ含めると、その列の像だけが元の像から除かれる。
方針：元の順序写像の単射性と集合の像の差を使う。
規約：削除後の部分語を別の列挙へ置き換えない。
使われ方：二つの削除順序の元の列の像の一致。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

lemma erase_composite_range {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (hf : Function.Injective f.orderHom) (j : Fin a.length) :
    Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion a j) ≫ f).orderHom = Set.range f.orderHom \ {f.orderHom j} := by
  change Set.range (f.orderHom ∘ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion a j).orderHom) = _
  rw [Set.range_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.eraseInclusion_range]
  simp only [Set.compl_eq_univ_sdiff, Set.image_sdiff hf, Set.image_univ, Set.image_singleton]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (erase_composite_range)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

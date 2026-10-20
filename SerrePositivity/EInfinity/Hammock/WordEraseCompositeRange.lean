module

public import SerrePositivity.EInfinity.Hammock.WordErasure
public import Mathlib.Data.Set.Lattice.Image

/-!
# 元の包含後に一列を削除した列の像

概要：部分語から一列を削除して元の語へ含めると、その列の像だけが元の像から除かれる。
方針：元の順序写像の単射性と集合の像の差を使う。
規約：削除後の部分語を別の列挙へ置き換えない。
使われ方：二つの削除順序の元の列の像の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

lemma erase_composite_range {a b : Word} (f : a ⟶ b)
    (hf : Function.Injective f.orderHom) (j : Fin a.length) :
    Set.range ((eraseInclusion a j) ≫ f).orderHom = Set.range f.orderHom \ {f.orderHom j} := by
  change Set.range (f.orderHom ∘ (eraseInclusion a j).orderHom) = _
  rw [Set.range_comp, eraseInclusion_range]
  simp only [Set.compl_eq_univ_sdiff, Set.image_sdiff hf, Set.image_univ, Set.image_singleton]

end SerrePositivity.EInfinity.Hammock.Word

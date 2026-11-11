module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
/-!
概要：符号付き単体反転と全順序写像の引き戻しに使う実添字比較。
方針：単調写像を両側から Fin.rev で挟み、像集合と局所単射性を照合する。
規約：基本面・退化だけでなく全順序写像を扱う。使われ方：反対模型の全自然性。
-/
@[expose] public section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {m n : ℕ}
/-- 任意の単調写像を両端で反転した、同じ単調写像。 -/
def reverseOrderHom (α : Fin (m + 1) →o Fin (n + 1)) : Fin (m + 1) →o Fin (n + 1) where
  toFun i := (α i.rev).rev
  monotone' _ _ h := Fin.rev_le_rev.mpr (α.monotone (Fin.rev_le_rev.mpr h))
@[simp] lemma reverseOrderHom_apply (α : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    reverseOrderHom α i = (α i.rev).rev := rfl
@[simp] lemma reverseOrderHom_reverse (α : Fin (m + 1) →o Fin (n + 1)) :
    reverseOrderHom (reverseOrderHom α) = α := by
  ext i
  simp
/-- 像を反転することと、元の集合と写像を同時に反転することは厳密に一致。 -/
lemma reverse_image (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse (I.image α) = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I).image (reverseOrderHom α) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse, Finset.image_image]
  apply Finset.image_congr
  intro i _
  simp only [Function.comp_apply, reverseOrderHom_apply, Fin.rev_rev]
/-- 反転は、実頂点部分集合上の局所単射性も双方向に保存する。 -/
lemma reverseOrderHom_injOn_iff (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) :
    Set.InjOn (reverseOrderHom α) (I : Set (Fin (m + 1))) ↔
      Set.InjOn α (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I : Set (Fin (m + 1))) := by
  constructor
  · intro h x hx y hy hxy
    apply Fin.rev_injective
    apply h ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse I x).mp hx) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse I y).mp hy)
    simpa only [reverseOrderHom_apply, Fin.rev_rev] using congrArg Fin.rev hxy
  · intro h x hx y hy hxy
    change x ∈ I at hx
    change y ∈ I at hy
    apply Fin.rev_injective
    apply h (by change x.rev ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I; simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse, Fin.rev_rev] using hx)
      (by change y.rev ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I; simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.mem_reverse, Fin.rev_rev] using hy)
    simpa only [reverseOrderHom_apply, Fin.rev_rev] using congrArg Fin.rev hxy
end SerrePositivity.InfinityCategories.Project.DerivedCategories

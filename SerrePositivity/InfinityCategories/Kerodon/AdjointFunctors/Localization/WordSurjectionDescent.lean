module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word

/-!
# 元の全射な語の写像からの色保存の降下

概要：全射の後で元の色を保つ順序写像は、終域でも元の色を保つ。
方針：各列の原像を使って元の色を回収する。
規約：全射性と順序写像の因子分解を明示して使う。
使われ方：混合縮約の可換四角形の残りの包含。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

/-- 元の全射の後で成り立つ色保存を回収する。 -/
def descendSurjection {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) (hf : Function.Surjective f.orderHom)
    (g : a ⟶ c) (h : Fin b.length →o Fin c.length)
    (he : ∀ i, h (f.orderHom i) = g.orderHom i) : b ⟶ c where
  orderHom := h
  direction_eq j := by
    obtain ⟨i, rfl⟩ := hf j
    exact (congrArg c.direction (he i)).trans
      ((g.direction_eq i).trans (f.direction_eq i).symm)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (descendSurjection)


lemma descendSurjection_fac {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    (hf : Function.Surjective f.orderHom) (g : a ⟶ c) (h : Fin b.length →o Fin c.length)
    (he : ∀ i, h (f.orderHom i) = g.orderHom i) :
    f ≫ descendSurjection f hf g h he = g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.hom_ext _ _ he

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (descendSurjection_fac)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Word

/-!
# 元の全射な語の写像からの色保存の降下

概要：全射の後で元の色を保つ順序写像は、終域でも元の色を保つ。
方針：各列の原像を使って元の色を回収する。
規約：全射性と順序写像の因子分解を明示して使う。
使われ方：混合縮約の可換四角形の残りの包含。
-/

@[expose] public section
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

/-- 元の全射の後で成り立つ色保存を回収する。 -/
def descendSurjection {a b c : Word} (f : a ⟶ b) (hf : Function.Surjective f.orderHom)
    (g : a ⟶ c) (h : Fin b.length →o Fin c.length)
    (he : ∀ i, h (f.orderHom i) = g.orderHom i) : b ⟶ c where
  orderHom := h
  direction_eq j := by
    obtain ⟨i, rfl⟩ := hf j
    exact (congrArg c.direction (he i)).trans
      ((g.direction_eq i).trans (f.direction_eq i).symm)

lemma descendSurjection_fac {a b c : Word} (f : a ⟶ b)
    (hf : Function.Surjective f.orderHom) (g : a ⟶ c) (h : Fin b.length →o Fin c.length)
    (he : ∀ i, h (f.orderHom i) = g.orderHom i) :
    f ≫ descendSurjection f hf g h he = g := hom_ext _ _ he

end SerrePositivity.EInfinity.Hammock.Word

module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostLaws
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorCurryHom

/-!
概要：底上の後合成を相対関手空間の任意の族の評価で計算する。
方針：fiber の包含の後合成則と内部 Hom の uncurry の自然性を使う。
規約：底と射影に充填条件は不要。
使われ方：一般の表現の相対写像空間比較の可換式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：相対後合成の後の族の評価は元の評価への全空間の射の後合成。
方針：相対関手空間の包含の計算を uncurry する。
規約：全高次パラメーターでの厳密な等式。
使われ方：比較の終点の族を相対後合成で表示する。 -/
lemma relativeFunctorPost_uncurry {A E F B K : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (a : A ⟶ B) (t : K ⟶ relativeFunctorSpace p a) :
    relativeFunctorUncurry (t ≫ HomotopyLimits.relativeFunctorPost p q f hf a) =
      relativeFunctorUncurry t ≫ f := by
  unfold relativeFunctorUncurry
  rw [Category.assoc, HomotopyLimits.relativeFunctorPost_ι, ← Category.assoc,
    uncurry_natural_right]

end SerrePositivity.InfinityCategories

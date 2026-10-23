module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverIsomorphism
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostUncurry
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSquarePost

/-!
概要：底上の始域・標的の同型で移した相対 Hom の族の評価を厳密に計算する。
方針：始域の逆同型の前合成と、標的の順同型の後合成へ展開する。
規約：任意のパラメーターを保ち、充填性を要求しない。
使われ方：unstraightening の底変換同型による、実際の相対引き戻し作用の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 全空間の底上の同型による相対 Hom の移送は、評価後に元の共役として読める。 -/
lemma relativeFunctorOverIso_uncurry {B T : SSet.{u}}
    {a a' p p' : Over B} (ea : a ≅ a') (ep : p ≅ p')
    (g : T ⟶ relativeFunctorSpace p.hom a.hom) :
    relativeFunctorUncurry (g ≫ (relativeFunctorOverIso ea ep).hom) =
      (ea.inv.left ▷ T) ≫ relativeFunctorUncurry g ≫ ep.hom.left := by
  rw [relativeFunctorOverIso_hom, ← Category.assoc, relativeFunctorPost_uncurry,
    relativeFunctorOverPre_uncurry, Category.assoc]

end SerrePositivity.InfinityCategories

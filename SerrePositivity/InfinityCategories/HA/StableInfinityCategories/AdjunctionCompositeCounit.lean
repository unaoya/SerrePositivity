module
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitLeftTriangle
/-!
概要：合成随伴の余単位を、同じ二余単位の whiskering の式へ展開する。
方針：双圏の結合子と単位子を明示し、同じ h Fun の射へ送る。
規約：指定余単位を保持する。使われ方：一般 kernel 随伴の余単位の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalClosed Bicategory SSet
/-- 合成随伴の余単位を、同じ二余単位の whiskering の式へ展開する。 -/
lemma bicategoryAdjunction_compCounit_explicit {T : Type u} [Bicategory.{w, v} T]
    {x y z : T} {f : x ⟶ y} {g : y ⟶ x} {f' : y ⟶ z} {g' : z ⟶ y}
    (a : Bicategory.Adjunction f g) (b : Bicategory.Adjunction f' g') :
    Bicategory.Adjunction.compCounit a b =
      (α_ g' g (f ≫ f')).hom ≫
        g' ◁ (α_ g f f').inv ≫ g' ◁ (a.counit ▷ f') ≫
          g' ◁ (λ_ f').hom ≫ b.counit := by
  unfold Bicategory.Adjunction.compCounit
  bicategory
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

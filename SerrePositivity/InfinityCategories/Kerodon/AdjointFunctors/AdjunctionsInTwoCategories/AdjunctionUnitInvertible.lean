module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.TriangleIdempotence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctNaturality

/-!
概要：可逆な余単位を持つ随伴の単位の whisker は可逆。
方針：三角恒等式で、単位の whisker に続く可逆因子を相殺する。
規約：任意の双圏で述べる。使われ方：B2 の反射像の局所性と反射される単位。

対応節は Kerodon 6.1（Tag 02CA）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Bicategory
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories

/-- 概要：余単位が可逆なら右随伴に沿った単位の制限は可逆。
方針：右三角恒等式の結合子と余単位の可逆因子を相殺する。
規約：単位そのものの可逆性は結論しない。
使われ方：反射部分圏の像での単位の可逆性。 -/
lemma bicategory_whiskerLeft_unit_isIso_of_counit
    {B : Type u} [Bicategory.{w, v} B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}
    (adj : Bicategory.Adjunction f g) [IsIso adj.counit] : IsIso (g ◁ adj.unit) := by
  have h : (g ◁ adj.unit) ≫ ((α_ g f g).inv ≫ adj.counit ▷ g) =
      (ρ_ g).hom ≫ (λ_ g).inv := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_rightZigzag_explicit]
    exact adj.right_triangle
  exact IsIso.of_isIso_fac_right h

/-- 概要：余単位が可逆なら左随伴で写した単位は可逆。
方針：左三角恒等式の結合子と余単位の可逆因子を相殺する。
規約：元の単位の whisker を保つ。
使われ方：局所化がその単位を反転することの一般補題。 -/
lemma bicategory_whiskerRight_unit_isIso_of_counit
    {B : Type u} [Bicategory.{w, v} B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}
    (adj : Bicategory.Adjunction f g) [IsIso adj.counit] : IsIso (adj.unit ▷ f) := by
  have h : (adj.unit ▷ f) ≫ ((α_ f g f).hom ≫ f ◁ adj.counit) =
      (λ_ f).hom ≫ (ρ_ f).inv := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.bicategory_leftZigzag_explicit]
    exact adj.left_triangle
  exact IsIso.of_isIso_fac_right h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories

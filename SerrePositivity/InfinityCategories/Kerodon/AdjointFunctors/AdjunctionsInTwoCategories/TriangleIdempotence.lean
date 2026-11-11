module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.Opposites

/-!
概要：右三角恒等式から左 zigzag の冪等性を得る。
方針：一胞体反対双圏で既存の反対側の冪等性定理を適用する。
規約：単位・余単位の可逆性は仮定しない。
使われ方：B1 の可逆な左 zigzag を恒等射と判定する。

対応節は Kerodon 6.1（Tag 02CA）。
-/

@[expose] public section
universe u v w
open CategoryTheory Bicategory
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories

/-- 概要：左 zigzag を結合子を明示した式で表す。
方針：双圏の coherence を揃える。
規約：任意の双圏。使われ方：厳密な双圏での三角恒等式の表示。 -/
lemma bicategory_leftZigzag_explicit
    {B : Type u} [Bicategory.{w, v} B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}
    (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :
    leftZigzag η ε = η ▷ f ≫ (α_ f g f).hom ≫ f ◁ ε := by bicategory

/-- 概要：右 zigzag を結合子を明示した式で表す。
方針：双圏の coherence を揃える。
規約：任意の双圏。使われ方：厳密な双圏での三角恒等式の表示。 -/
lemma bicategory_rightZigzag_explicit
    {B : Type u} [Bicategory.{w, v} B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}
    (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :
    rightZigzag η ε = g ◁ η ≫ (α_ g f g).inv ≫ ε ▷ g := by bicategory

/-- 概要：右三角恒等式があれば左 zigzag は双圏の合成で冪等。
方針：一胞体反対双圏で右 zigzag の冪等性を使い、coherence を揃えて戻す。
規約：任意の双圏。単位・余単位に可逆性は不要。
使われ方：可逆な左 zigzag から左三角恒等式を得る。 -/
lemma bicategory_leftZigzag_idempotent_of_right_triangle
    {B : Type u} [Bicategory.{w, v} B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}
    (η : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b)
    (hR : rightZigzag η ε = (ρ_ g).hom ≫ (λ_ g).inv) :
    leftZigzag η ε ⊗≫ leftZigzag η ε = leftZigzag η ε := by
  have hop : leftZigzag (Bicategory.Opposite.op2 η) (Bicategory.Opposite.op2 ε) =
      (λ_ g.op).hom ≫ (ρ_ g.op).inv := by
    apply congrArg (Bicategory.Opposite.op2 (a := b) (b := a))
    change _ = (ρ_ g).hom ≫ (λ_ g).inv
    simpa [leftZigzag, rightZigzag, bicategoricalComp] using hR
  have h := rightZigzag_idempotent_of_left_triangle (B := Bᵒᵖ) (f := g.op) (g := f.op)
    (Bicategory.Opposite.op2 η) (Bicategory.Opposite.op2 ε) hop
  have hh := congrArg Bicategory.Opposite.Hom2.unop2 h
  simpa [leftZigzag, rightZigzag, bicategoricalComp] using hh

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories

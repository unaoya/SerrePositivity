module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrecompositionFlipHom

/-!
概要：随伴の Hom₁ の逆対応の三つの自然性。
方針：単位の whisker 表示と双圏の交換則を使う。
規約：一般の双圏で結合子を明示し、元の二胞体を保持する。
使われ方：前合成の全パラメータ Hom 対応の自然性。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe w v u
open CategoryTheory Bicategory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：Hom₁ の逆対応は標的の二胞体の合成に自然。
方針：単位による表示と左 whisker の合成保存を使う。
規約：一般の双圏の結合子を保持する。
使われ方：前合成随伴の標的自然性。 -/
lemma adjointHomOneSymm_comp {B : Type u} [Bicategory.{w, v} B]
    {b c d : B} {l : b ⟶ c} {r : c ⟶ b} (a : l ⊣ r)
    {g : b ⟶ d} {h h' : c ⟶ d} (α : r ≫ g ⟶ h) (β : h ⟶ h') :
    a.homEquiv₁.symm (α ≫ β) = a.homEquiv₁.symm α ≫ l ◁ β := by
  simp only [Adjunction.homEquiv₁_symm_apply, whiskerLeft_comp, Category.assoc]

/-- 概要：Hom₁ の逆対応は始域の二胞体の合成に自然。
方針：単位と二胞体の交換則を適用し結合子を整える。
規約：同じ随伴と元の二胞体を使う。
使われ方：前合成随伴の始域自然性。 -/
lemma adjointHomOneSymm_precomp {B : Type u} [Bicategory.{w, v} B]
    {b c d : B} {l : b ⟶ c} {r : c ⟶ b} (a : l ⊣ r)
    {g g' : b ⟶ d} {h : c ⟶ d} (γ : g' ⟶ g) (α : r ≫ g ⟶ h) :
    a.homEquiv₁.symm (r ◁ γ ≫ α) = γ ≫ a.homEquiv₁.symm α := by
  simp only [Adjunction.homEquiv₁_symm_apply, whiskerLeft_comp]
  calc
    _ = (λ_ g').inv ≫ (a.unit ▷ g' ≫ (l ≫ r) ◁ γ) ≫
      (α_ l r g).hom ≫ l ◁ α := by bicategory
    _ = (λ_ g').inv ≫ ((𝟙 b) ◁ γ ≫ a.unit ▷ g) ≫
      (α_ l r g).hom ≫ l ◁ α := by rw [← whisker_exchange]
    _ = _ := by bicategory

/-- 概要：Hom₁ の逆対応は関手による後合成に自然。
方針：単位の表示を展開し双圏の結合子の整合を使う。
規約：合成の括弧の差を結合子で明示する。
使われ方：前合成随伴のパラメータ自然性。 -/
lemma adjointHomOneSymm_whiskerRight {B : Type u} [Bicategory.{w, v} B]
    {b c d e : B} {l : b ⟶ c} {r : c ⟶ b} (a : l ⊣ r)
    {g : b ⟶ d} {h : c ⟶ d} (α : r ≫ g ⟶ h) (k : d ⟶ e) :
    a.homEquiv₁.symm ((α_ r g k).inv ≫ α ▷ k) =
      (a.homEquiv₁.symm α) ▷ k ≫ (α_ l h k).hom := by
  simp only [Adjunction.homEquiv₁_symm_apply]
  bicategory

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConjugateUnit

/-!
概要：随伴の正方形の mate と、元の二つの指定単位との整合性。
方針：交換則二回と元の三角恒等式で、同じ全二胞体の等式を示す。
使われ方：HTT §5.2.2、Kerodon §6.2（Tag 02EH）の層化と site 再添字の単位の比較。
規約：一般の双圏で、元の結合子・単位子を自動挿入して型に保持する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Bicategory
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 元の正方形の mate は、二つの指定単位の正方形を全二胞体として可換にする。 -/
lemma bicategory_unit_mateEquiv {B : Type u} [Bicategory.{w, v} B]
    {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}
    {g : a ⟶ c} {h : b ⟶ d} (s : l₁ ⊣ r₁) (t : l₂ ⊣ r₂)
    (α : g ≫ l₂ ⟶ l₁ ≫ h) :
    𝟙 g ⊗≫ s.unit ▷ g ⊗≫ l₁ ◁ mateEquiv s t α ⊗≫ 𝟙 ((l₁ ≫ h) ≫ r₂) =
      𝟙 g ⊗≫ g ◁ t.unit ⊗≫ α ▷ r₂ ⊗≫ 𝟙 ((l₁ ≫ h) ≫ r₂) := by
  calc
    𝟙 g ⊗≫ s.unit ▷ g ⊗≫ l₁ ◁ mateEquiv s t α ⊗≫ 𝟙 ((l₁ ≫ h) ≫ r₂) =
      𝟙 g ⊗≫ (s.unit ▷ (g ≫ 𝟙 c) ≫ (l₁ ≫ r₁) ◁ (g ◁ t.unit)) ⊗≫
        (l₁ ◁ r₁ ◁ α) ▷ r₂ ⊗≫ ((l₁ ◁ s.counit) ▷ h) ▷ r₂ ⊗≫
          𝟙 ((l₁ ≫ h) ≫ r₂) := by
      rw [mateEquiv_apply' s t α]
      bicategory
    _ = 𝟙 g ⊗≫ ((𝟙 a) ◁ (g ◁ t.unit) ≫ s.unit ▷ (g ≫ (l₂ ≫ r₂))) ⊗≫
        (l₁ ◁ r₁ ◁ α) ▷ r₂ ⊗≫ ((l₁ ◁ s.counit) ▷ h) ▷ r₂ ⊗≫
          𝟙 ((l₁ ≫ h) ≫ r₂) := by rw [← whisker_exchange s.unit (g ◁ t.unit)]
    _ = 𝟙 g ⊗≫ g ◁ t.unit ⊗≫ (s.unit ▷ (g ≫ l₂) ≫ (l₁ ≫ r₁) ◁ α) ▷ r₂ ⊗≫
        ((l₁ ◁ s.counit) ▷ h) ▷ r₂ ⊗≫ 𝟙 ((l₁ ≫ h) ≫ r₂) := by bicategory
    _ = 𝟙 g ⊗≫ g ◁ t.unit ⊗≫ ((𝟙 a) ◁ α ≫ s.unit ▷ (l₁ ≫ h)) ▷ r₂ ⊗≫
        ((l₁ ◁ s.counit) ▷ h) ▷ r₂ ⊗≫ 𝟙 ((l₁ ≫ h) ≫ r₂) := by
      rw [← whisker_exchange s.unit α]
    _ = 𝟙 g ⊗≫ g ◁ t.unit ⊗≫ α ▷ r₂ ⊗≫
        (leftZigzag s.unit s.counit ▷ h) ▷ r₂ ⊗≫ 𝟙 ((l₁ ≫ h) ≫ r₂) := by bicategory
    _ = _ := by rw [s.left_triangle]; bicategory

/-- 逆 mate でも同じ指定単位の全正方形を保持する。 -/
lemma bicategory_unit_mateEquiv_symm {B : Type u} [Bicategory.{w, v} B]
    {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}
    {g : a ⟶ c} {h : b ⟶ d} (s : l₁ ⊣ r₁) (t : l₂ ⊣ r₂)
    (β : r₁ ≫ g ⟶ h ≫ r₂) :
    𝟙 g ⊗≫ s.unit ▷ g ⊗≫ l₁ ◁ β ⊗≫ 𝟙 ((l₁ ≫ h) ≫ r₂) =
      𝟙 g ⊗≫ g ◁ t.unit ⊗≫ (mateEquiv s t).symm β ▷ r₂ ⊗≫
        𝟙 ((l₁ ≫ h) ≫ r₂) := by
  simpa only [Equiv.apply_symm_apply] using
    bicategory_unit_mateEquiv s t ((mateEquiv s t).symm β)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

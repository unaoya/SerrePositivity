module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctNaturality

/-!
概要：随伴間の conjugate による全二胞体比較が、指定した単位を保つことを示す。
方針：交換則を二度使い、元の随伴の三角恒等式へ帰着する。
使われ方：HTT §5.2.2、Kerodon §6.2（Tag 02EH）の随伴の比較の単位法則。
規約：単位や余単位を新たに選び直さない。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Bicategory
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 左二胞体の conjugate の単位との整合性。任意の双圏での既存の構成の法則。 -/
lemma bicategory_unit_conjugateEquiv {B : Type u} [Bicategory.{w, v} B]
    {c d : B} {l₁ l₂ : c ⟶ d} {r₁ r₂ : d ⟶ c}
    (a : l₁ ⊣ r₁) (b : l₂ ⊣ r₂) (α : l₂ ⟶ l₁) :
    a.unit ≫ l₁ ◁ conjugateEquiv a b α = b.unit ≫ α ▷ r₂ := by
  calc
    a.unit ≫ l₁ ◁ conjugateEquiv a b α = 𝟙 (𝟙 c) ⊗≫ (a.unit ▷ 𝟙 c ≫ (l₁ ≫ r₁) ◁ b.unit) ⊗≫
        (l₁ ◁ r₁ ◁ α) ▷ r₂ ⊗≫ (l₁ ◁ a.counit) ▷ r₂ ⊗≫ 𝟙 (l₁ ≫ r₂) := by
      rw [conjugateEquiv_apply']
      bicategory
    _ = 𝟙 (𝟙 c) ⊗≫ ((𝟙 c) ◁ b.unit ≫ a.unit ▷ (l₂ ≫ r₂)) ⊗≫
        (l₁ ◁ r₁ ◁ α) ▷ r₂ ⊗≫ (l₁ ◁ a.counit) ▷ r₂ ⊗≫ 𝟙 (l₁ ≫ r₂) := by
      rw [← whisker_exchange]
    _ = b.unit ⊗≫ (a.unit ▷ l₂ ≫ (l₁ ≫ r₁) ◁ α) ▷ r₂ ⊗≫
        (l₁ ◁ a.counit) ▷ r₂ ⊗≫ 𝟙 (l₁ ≫ r₂) := by bicategory
    _ = b.unit ⊗≫ ((𝟙 c) ◁ α ≫ a.unit ▷ l₁) ▷ r₂ ⊗≫
        (l₁ ◁ a.counit) ▷ r₂ ⊗≫ 𝟙 (l₁ ≫ r₂) := by rw [← whisker_exchange]
    _ = b.unit ⊗≫ α ▷ r₂ ⊗≫ (leftZigzag a.unit a.counit) ▷ r₂ ⊗≫ 𝟙 (l₁ ≫ r₂) := by
      bicategory
    _ = _ := by rw [a.left_triangle]; bicategory

/-- 逆 conjugate でも、同じ指定単位の等式を保つ。 -/
lemma bicategory_unit_conjugateEquiv_symm {B : Type u} [Bicategory.{w, v} B]
    {c d : B} {l₁ l₂ : c ⟶ d} {r₁ r₂ : d ⟶ c}
    (a : l₁ ⊣ r₁) (b : l₂ ⊣ r₂) (β : r₁ ⟶ r₂) :
    a.unit ≫ l₁ ◁ β = b.unit ≫ ((conjugateEquiv a b).symm β) ▷ r₂ := by
  simpa only [Equiv.apply_symm_apply] using
    bicategory_unit_conjugateEquiv a b ((conjugateEquiv a b).symm β)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

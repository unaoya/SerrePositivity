module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.MateUnit

/-!
概要：同値を縦に持つ随伴の正方形で、元の指定二胞体を保つ可逆な mate を作る。
方針：Mathlib の二重 mate と conjugateIsoEquiv の全単射を直接合成する。
使われ方：HTT §5.2.2、Kerodon §6.2（Tag 02EH）の層化の指定単位を保つ site 比較。
規約：与えた随伴・単位・正方形を保持し、別の逆同値を選ばない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Bicategory
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
variable {B : Type u} [Bicategory.{w, v} B]
variable {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a} {l₂ : c ⟶ d} {r₂ : d ⟶ c}
variable {f₁ : a ⟶ c} {u₁ : c ⟶ a} {f₂ : b ⟶ d} {u₂ : d ⟶ b}

/-- 縦の同値の随伴に沿う mate は、元の指定同型から同じ可逆二胞体になる。 -/
def verticalSquareMateIso (p : f₁ ⊣ u₁) (q : f₂ ⊣ u₂)
    [IsIso p.unit] [IsIso q.counit] (β : r₁ ≫ f₁ ≅ f₂ ≫ r₂) :
    u₂ ≫ r₁ ≅ r₂ ≫ u₁ := by
  haveI : IsIso (mateEquiv q p β.hom) := by
    rw [Bicategory.mateEquiv_apply' q p β.hom]
    dsimp only [bicategoricalComp]
    infer_instance
  exact asIso (mateEquiv q p β.hom)

/-- 二重 mate の既存の全単射による、指定正方形の可逆な横の mate。 -/
def equivalenceSquareMateIso (s : l₁ ⊣ r₁) (t : l₂ ⊣ r₂)
    (p : f₁ ⊣ u₁) (q : f₂ ⊣ u₂) [IsIso p.unit] [IsIso q.counit]
    (β : r₁ ≫ f₁ ≅ f₂ ≫ r₂) : f₁ ≫ l₂ ≅ l₁ ≫ f₂ :=
  (conjugateIsoEquiv (s.comp q) (p.comp t)).symm (verticalSquareMateIso p q β)

/-- 同じ横の mate は、元の指定した正方形の二胞体そのものへ戻る。 -/
lemma equivalenceSquareMateIso_mate (s : l₁ ⊣ r₁) (t : l₂ ⊣ r₂)
    (p : f₁ ⊣ u₁) (q : f₂ ⊣ u₂) [IsIso p.unit] [IsIso q.counit]
    (β : r₁ ≫ f₁ ≅ f₂ ≫ r₂) :
    mateEquiv s t (equivalenceSquareMateIso s t p q β).hom = β.hom := by
  apply (mateEquiv q p).injective
  rw [Bicategory.iterated_mateEquiv_conjugateEquiv]
  exact congrArg (fun k ↦ k.hom)
    ((conjugateIsoEquiv (s.comp q) (p.comp t)).apply_symm_apply
      (verticalSquareMateIso p q β))

/-- 指定した正方形と元の二つの単位を保つ、横の可逆比較の全二胞体の法則。 -/
lemma equivalenceSquareMateIso_unit (s : l₁ ⊣ r₁) (t : l₂ ⊣ r₂)
    (p : f₁ ⊣ u₁) (q : f₂ ⊣ u₂) [IsIso p.unit] [IsIso q.counit]
    (β : r₁ ≫ f₁ ≅ f₂ ≫ r₂) :
    𝟙 f₁ ⊗≫ s.unit ▷ f₁ ⊗≫ l₁ ◁ β.hom ⊗≫ 𝟙 ((l₁ ≫ f₂) ≫ r₂) =
      𝟙 f₁ ⊗≫ f₁ ◁ t.unit ⊗≫ (equivalenceSquareMateIso s t p q β).hom ▷ r₂ ⊗≫
        𝟙 ((l₁ ≫ f₂) ≫ r₂) := by
  have h := bicategory_unit_mateEquiv s t (equivalenceSquareMateIso s t p q β).hom
  rw [equivalenceSquareMateIso_mate] at h
  exact h

/-- 横の比較の逆を後合成すると、元の単位の可換正方形を得る。 -/
lemma equivalenceSquareMateIso_inverse_unit (s : l₁ ⊣ r₁) (t : l₂ ⊣ r₂)
    (p : f₁ ⊣ u₁) (q : f₂ ⊣ u₂) [IsIso p.unit] [IsIso q.counit]
    (β : r₁ ≫ f₁ ≅ f₂ ≫ r₂) :
    𝟙 f₁ ⊗≫ s.unit ▷ f₁ ⊗≫ l₁ ◁ β.hom ⊗≫
        (equivalenceSquareMateIso s t p q β).inv ▷ r₂ ⊗≫ 𝟙 (f₁ ≫ (l₂ ≫ r₂)) =
      𝟙 f₁ ⊗≫ f₁ ◁ t.unit ⊗≫ 𝟙 (f₁ ≫ (l₂ ≫ r₂)) := by
  let α := equivalenceSquareMateIso s t p q β
  have h := equivalenceSquareMateIso_unit s t p q β
  calc
    _ = (𝟙 f₁ ⊗≫ s.unit ▷ f₁ ⊗≫ l₁ ◁ β.hom ⊗≫ 𝟙 ((l₁ ≫ f₂) ≫ r₂)) ⊗≫
        α.inv ▷ r₂ ⊗≫ 𝟙 (f₁ ≫ (l₂ ≫ r₂)) := by bicategory
    _ = (𝟙 f₁ ⊗≫ f₁ ◁ t.unit ⊗≫ α.hom ▷ r₂ ⊗≫ 𝟙 ((l₁ ≫ f₂) ≫ r₂)) ⊗≫
        α.inv ▷ r₂ ⊗≫ 𝟙 (f₁ ≫ (l₂ ≫ r₂)) := by rw [h]
    _ = 𝟙 f₁ ⊗≫ f₁ ◁ t.unit ⊗≫ (α.hom ▷ r₂ ≫ α.inv ▷ r₂) ⊗≫
        𝟙 (f₁ ≫ (l₂ ≫ r₂)) := by bicategory
    _ = _ := by rw [hom_inv_whiskerRight]; bicategory

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

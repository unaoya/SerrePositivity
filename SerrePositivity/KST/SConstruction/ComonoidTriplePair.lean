module
public import SerrePositivity.KST.SConstruction.ComonoidTensorDiagonal

/-! # 元の余モノイドからの三つの出力の結合則
概要：同じ元の対角を使う三出力の束ね方が、元の結合同型を介して一致する。
方針：対角の結合則と tensor の自然性で、元の三つの出力写像を保持する。
規約：出力の順序を保つ。使われ方：Λ の実 oplax tensor の結合則。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open scoped ComonObj
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- 元の対角からの三つの出力は、元の結合同型を介して同じ束ね方を与える。 -/
lemma comonoidTriplePair (P : Comon C) {X Y Z : C}
    (a : P.X ⟶ X) (b : P.X ⟶ Y) (c : P.X ⟶ Z) :
    (Δ[P.X] ≫ ((Δ[P.X] ≫ (a ⊗ₘ b)) ⊗ₘ c)) ≫ (α_ X Y Z).hom =
      Δ[P.X] ≫ (a ⊗ₘ (Δ[P.X] ≫ (b ⊗ₘ c))) := by
  calc
    _ = (Δ[P.X] ≫ Δ[P.X] ▷ P.X) ≫
        (((a ⊗ₘ b) ⊗ₘ c) ≫ (α_ X Y Z).hom) := by
      rw [← whiskerRight_comp_tensorHom]
      simp only [Category.assoc]
    _ = (Δ[P.X] ≫ Δ[P.X] ▷ P.X) ≫
        (α_ P.X P.X P.X).hom ≫ (a ⊗ₘ (b ⊗ₘ c)) := by
      rw [associator_naturality]
    _ = (Δ[P.X] ≫ P.X ◁ Δ[P.X]) ≫ (a ⊗ₘ (b ⊗ₘ c)) := by
      rw [← Category.assoc, Category.assoc Δ[P.X], ← ComonObj.comul_assoc]
    _ = _ := by
      rw [Category.assoc, whiskerLeft_comp_tensorHom]

/-- 元の第一出力の余モノイド射を二つに分けると、元の二つの合成を回収する。 -/
lemma comonoidPair_split_left {P Q : Comon C} {X Y Z : C}
    (f : P ⟶ Q) (c : P.X ⟶ Z) (a : Q.X ⟶ X) (b : Q.X ⟶ Y) :
    (Δ[P.X] ≫ (f.hom ⊗ₘ c)) ≫ ((Δ[Q.X] ≫ (a ⊗ₘ b)) ⊗ₘ 𝟙 Z) =
      Δ[P.X] ≫ ((Δ[P.X] ≫ ((f.hom ≫ a) ⊗ₘ (f.hom ≫ b))) ⊗ₘ c) := by
  rw [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id,
    comonoidPair_precompose]

/-- 元の第二出力の余モノイド射を二つに分けると、元の二つの合成を回収する。 -/
lemma comonoidPair_split_right {P Q : Comon C} {X Y Z : C}
    (a : P.X ⟶ X) (f : P ⟶ Q) (b : Q.X ⟶ Y) (c : Q.X ⟶ Z) :
    (Δ[P.X] ≫ (a ⊗ₘ f.hom)) ≫ (𝟙 X ⊗ₘ (Δ[Q.X] ≫ (b ⊗ₘ c))) =
      Δ[P.X] ≫ (a ⊗ₘ (Δ[P.X] ≫ ((f.hom ≫ b) ⊗ₘ (f.hom ≫ c)))) := by
  rw [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id,
    comonoidPair_precompose]

/-- 元の三つの出力の束ね方は、元の余モノイド射の前合成を保つ。 -/
lemma comonoidTripleRight_precompose {P Q : Comon C} {X Y Z : C}
    (f : P ⟶ Q) (a : Q.X ⟶ X) (b : Q.X ⟶ Y) (c : Q.X ⟶ Z) :
    f.hom ≫ Δ[Q.X] ≫ (a ⊗ₘ (Δ[Q.X] ≫ (b ⊗ₘ c))) =
      Δ[P.X] ≫ ((f.hom ≫ a) ⊗ₘ (Δ[P.X] ≫ ((f.hom ≫ b) ⊗ₘ (f.hom ≫ c)))) := by
  rw [comonoidPair_precompose, comonoidPair_precompose]

end SerrePositivity.KST.SConstruction

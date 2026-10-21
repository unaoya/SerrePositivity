module
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # 元の tensor 連結比較の結合と単位の帰納段階
概要：三ブロックの連結比較の可換性を、右端を一つ加えた比較へ移す。
方針：元の比較を tensor し、同じ結合同型の五角と単位の自然性を使う。
規約：因子の交換を使わない。使われ方：反復 tensor 冪の元の結合・単位の法則。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- 零個の第三ブロックに対する、元の右単位による結合比較。 -/
lemma monoidalPowerCoherence_unit {R X Y : C} (d : R ⟶ X ⊗ Y) :
    d ≫ (𝟙 X ⊗ₘ (ρ_ Y).inv) =
      (ρ_ R).inv ≫ (d ⊗ₘ 𝟙 (𝟙_ C)) ≫ (α_ X Y (𝟙_ C)).hom := by
  rw [id_tensor_rightUnitor_inv]
  simpa only [tensorHom_id, Category.assoc] using
    congrArg (fun t => t ≫ (α_ X Y (𝟙_ C)).hom) (rightUnitor_inv_naturality d)

/-- 三ブロックの元の可換式を、右端を一つ加えた連結比較へ移す。 -/
lemma monoidalPowerCoherence_step {R S U V X Y Z I : C}
    (a : R ⟶ S) (b : S ⟶ X ⊗ V) (c : V ⟶ Y ⊗ Z)
    (d : R ⟶ U ⊗ Z) (e : U ⟶ X ⊗ Y)
    (h : a ≫ b ≫ (𝟙 X ⊗ₘ c) = d ≫ (e ⊗ₘ 𝟙 Z) ≫ (α_ X Y Z).hom) :
    (a ⊗ₘ 𝟙 I) ≫ (b ⊗ₘ 𝟙 I) ≫ (α_ X V I).hom ≫
        (𝟙 X ⊗ₘ ((c ⊗ₘ 𝟙 I) ≫ (α_ Y Z I).hom)) =
      (d ⊗ₘ 𝟙 I) ≫ (α_ U Z I).hom ≫ (e ⊗ₘ 𝟙 (Z ⊗ I)) ≫ (α_ X Y (Z ⊗ I)).hom := by
  calc
    _ = ((a ≫ b ≫ (𝟙 X ⊗ₘ c)) ⊗ₘ 𝟙 I) ≫
        (α_ X (Y ⊗ Z) I).hom ≫ (𝟙 X ⊗ₘ (α_ Y Z I).hom) := by monoidal
    _ = ((d ≫ (e ⊗ₘ 𝟙 Z) ≫ (α_ X Y Z).hom) ⊗ₘ 𝟙 I) ≫
        (α_ X (Y ⊗ Z) I).hom ≫ (𝟙 X ⊗ₘ (α_ Y Z I).hom) := by rw [h]
    _ = _ := by monoidal

/-- 元の比較同型を展開せずに保つ、三ブロック結合の一段更新。 -/
lemma monoidalPowerCoherence_step_iso {R S U V X Y Z I : C}
    (a : R ⟶ S) (b : S ≅ X ⊗ V) (c : V ≅ Y ⊗ Z)
    (d : R ≅ U ⊗ Z) (e : U ≅ X ⊗ Y)
    (h : a ≫ b.hom ≫ (𝟙 X ⊗ₘ c.hom) = d.hom ≫ (e.hom ⊗ₘ 𝟙 Z) ≫ (α_ X Y Z).hom) :
    (a ⊗ₘ 𝟙 I) ≫ ((b ⊗ᵢ Iso.refl I) ≪≫ α_ X V I).hom ≫
        (𝟙 X ⊗ₘ ((c ⊗ᵢ Iso.refl I) ≪≫ α_ Y Z I).hom) =
      ((d ⊗ᵢ Iso.refl I) ≪≫ α_ U Z I).hom ≫
        (e.hom ⊗ₘ 𝟙 (Z ⊗ I)) ≫ (α_ X Y (Z ⊗ I)).hom := by
  simpa only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Category.assoc] using
    monoidalPowerCoherence_step a b.hom c.hom d.hom e.hom h

/-- 全対象を固定した、元の三ブロック比較の可換式。 -/
def MonoidalPowerCoherenceEquation {R S U V X Y Z : C}
    (a : R ⟶ S) (b : S ≅ X ⊗ V) (c : V ≅ Y ⊗ Z)
    (d : R ≅ U ⊗ Z) (e : U ≅ X ⊗ Y) : Prop :=
  a ≫ b.hom ≫ (𝟙 X ⊗ₘ c.hom) = d.hom ≫ (e.hom ⊗ₘ 𝟙 Z) ≫ (α_ X Y Z).hom

/-- 元の比較同型を保った、右端を一つ加えた三ブロックの可換式。 -/
def MonoidalPowerCoherenceStepEquation {R S U V X Y Z I : C}
    (a : R ⟶ S) (b : S ≅ X ⊗ V) (c : V ≅ Y ⊗ Z)
    (d : R ≅ U ⊗ Z) (e : U ≅ X ⊗ Y) : Prop :=
  MonoidalPowerCoherenceEquation
    (R := R ⊗ I) (S := S ⊗ I) (U := U) (V := V ⊗ I)
    (X := X) (Y := Y) (Z := Z ⊗ I)
    (a ⊗ₘ 𝟙 I) ((b ⊗ᵢ Iso.refl I) ≪≫ α_ X V I)
    ((c ⊗ᵢ Iso.refl I) ≪≫ α_ Y Z I) ((d ⊗ᵢ Iso.refl I) ≪≫ α_ U Z I) e

/-- 元の三ブロックの可換性から、同じ同型を保った更新の可換式を得る。 -/
lemma monoidalPowerCoherence_step_equation {R S U V X Y Z I : C}
    (a : R ⟶ S) (b : S ≅ X ⊗ V) (c : V ≅ Y ⊗ Z)
    (d : R ≅ U ⊗ Z) (e : U ≅ X ⊗ Y)
    (h : a ≫ b.hom ≫ (𝟙 X ⊗ₘ c.hom) = d.hom ≫ (e.hom ⊗ₘ 𝟙 Z) ≫ (α_ X Y Z).hom) :
    MonoidalPowerCoherenceStepEquation (I := I) a b c d e :=
  monoidalPowerCoherence_step_iso a b c d e h

/-- 元の左単位比較は、右端を一つ加えた同じ連結比較と可換。 -/
lemma monoidalPowerCoherence_leftUnit_step {R Y I : C} (d : R ⟶ (𝟙_ C) ⊗ Y) :
    ((d ⊗ₘ 𝟙 I) ≫ (α_ (𝟙_ C) Y I).hom) ≫ (λ_ (Y ⊗ I)).hom =
      (d ≫ (λ_ Y).hom) ⊗ₘ 𝟙 I := by
  monoidal

/-- 元の零段の左右単位の比較。 -/
lemma monoidalPowerCoherence_leftUnit_zero :
    𝟙 (𝟙_ C) = (ρ_ (𝟙_ C)).inv ≫ (λ_ (𝟙_ C)).hom := by
  monoidal_coherence

end SerrePositivity.KST.SConstruction

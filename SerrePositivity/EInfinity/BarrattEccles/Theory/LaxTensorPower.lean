module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Blocks
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Lax monoidal 関手と反復テンソル

## 概要
Berger–Moerdijk §1 の演算を lax monoidal 関手に沿って移すためのテンソル冪の比較。

## 方針
零因子では単位、一因子を増やすときは tensorator を使う。

## 規約
テンソル冪の括り方と arity の移送は既存の TensorPowers に従う。

## 使われ方
Barratt–Eccles 代数の係数制限。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v u' v'

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory TensorPowers
open Functor.LaxMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal]

/-- lax monoidal 関手が誘導する、同じ括り方のテンソル冪の比較。 -/
def laxPowerComparison (X : C) : ∀ n : ℕ, power (F.obj X) n ⟶ F.obj (power X n)
  | 0 => ε F
  | n + 1 => (F.obj X ◁ laxPowerComparison X n) ≫ μ F X (power X n)

/-- テンソル冪の比較は対象の射に関して自然。 -/
@[reassoc]
lemma laxPowerComparison_naturality {X Y : C} (g : X ⟶ Y) (n : ℕ) :
    TensorPowers.map (F.map g) n ≫ laxPowerComparison F Y n =
      laxPowerComparison F X n ≫ F.map (TensorPowers.map g n) := by
  induction n with
  | zero =>
    change 𝟙 (𝟙_ D) ≫ ε F = ε F ≫ F.map (𝟙 (𝟙_ C))
    rw [Category.id_comp, F.map_id, Category.comp_id]
  | succ n ih =>
    simp only [TensorPowers.map, laxPowerComparison, Category.assoc]
    rw [tensorHom_comp_whiskerLeft_assoc, ih, ← whiskerLeft_comp_tensorHom_assoc]
    exact congrArg (fun k => (F.obj X ◁ laxPowerComparison F X n) ≫ k)
      (μ_natural F g (TensorPowers.map g n))

/-- テンソル冪の比較は、次数の等式で与えられる移送と可換。 -/
@[reassoc]
lemma laxPowerComparison_index (X : C) {n m : ℕ} (h : n = m) :
    eqToHom (congrArg (power (F.obj X)) h) ≫ laxPowerComparison F X m =
      laxPowerComparison F X n ≫ F.map (eqToHom (congrArg (power X) h)) := by
  subst m
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, F.map_id, Category.comp_id]

/-- tensorator の結合律を、各因子を写す前の対象から計算する。 -/
@[reassoc]
lemma laxTensorator_associativity {U V W : C} {U' V' W' : D}
    (a : U' ⟶ F.obj U) (b : V' ⟶ F.obj V) (c : W' ⟶ F.obj W) :
    ((a ⊗ₘ b) ⊗ₘ c) ≫ (μ F U V ▷ F.obj W) ≫
        μ F (U ⊗ V) W ≫ F.map (α_ U V W).hom =
      (α_ U' V' W').hom ≫ (a ⊗ₘ ((b ⊗ₘ c) ≫ μ F V W)) ≫ μ F U (V ⊗ W) := by
  rw [associativity, associator_naturality_assoc, tensorHom_comp_whiskerLeft_assoc]

/-- 反復テンソルの二つのブロックを連結しても比較写像は同じ。 -/
lemma laxPowerComparison_append (X : C) (m n : ℕ) :
    (laxPowerComparison F X m ⊗ₘ laxPowerComparison F X n) ≫
        μ F (power X m) (power X n) ≫ F.map (appendIso X m n).hom =
      (appendIso (F.obj X) m n).hom ≫ laxPowerComparison F X (m + n) := by
  induction m with
  | zero =>
    simp only [appendIso, laxPowerComparison, power, Iso.trans_hom, eqToIso.hom,
      Category.assoc, Functor.map_comp]
    rw [laxPowerComparison_index F X (Nat.zero_add n).symm, tensorHom_def',
      Category.assoc, ← left_unitality_assoc, leftUnitor_naturality_assoc]
  | succ m ih =>
    let a := laxPowerComparison F X m
    let b := laxPowerComparison F X n
    simp only [appendIso, laxPowerComparison, power, Iso.trans_hom, eqToIso.hom,
      whiskerLeftIso_hom, Category.assoc, Functor.map_comp]
    rw [laxPowerComparison_index F X (Nat.succ_add m n).symm]
    have h : (((F.obj X) ◁ a ≫ μ F X (power X m)) ⊗ₘ b) =
        (((𝟙 (F.obj X)) ⊗ₘ a) ⊗ₘ b) ≫ (μ F X (power X m) ▷ F.obj (power X n)) := by
      rw [← tensorHom_comp_whiskerRight, id_tensorHom]
    rw [h, Category.assoc, laxTensorator_associativity_assoc, id_tensorHom]
    rw [← μ_natural_right_assoc, ← whiskerLeft_comp_assoc]
    simp only [Category.assoc]
    rw [ih, whiskerLeft_comp, Category.assoc, laxPowerComparison]
    simp only [Category.assoc]

/-- 一因子のテンソル冪の比較は右単位子を保つ。 -/
@[reassoc]
lemma laxPowerComparison_one (X : C) :
    laxPowerComparison F X 1 ≫ F.map (TensorPowers.oneIso X).hom =
      (TensorPowers.oneIso (F.obj X)).hom := by
  change ((F.obj X ◁ ε F) ≫ μ F X (𝟙_ C)) ≫ F.map (ρ_ X).hom = (ρ_ (F.obj X)).hom
  rw [Category.assoc, ← right_unitality]

end SerrePositivity.EInfinity

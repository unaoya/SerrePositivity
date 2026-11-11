module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.LaxTensorPower

/-!
# Lax monoidal 関手のテンソル比較の合成

## 概要
Berger–Moerdijk §1 のオペラッド代数の入力の括り直しと交換を比較する。

## 方針
各因子の比較の後に tensorator を適用し、構造射と可換な四角形を合成する。

## 規約
比較射に可逆性を仮定しない。

## 使われ方
代数の入力置換と部分合成を係数制限する。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v u' v'

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open Functor.LaxMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  (F : C ⥤ D)

section Monoidal

variable [F.LaxMonoidal]

/-- 二つの因子の比較からテンソルの比較を作る。 -/
def laxTensorComparison {A B : C} {A' B' : D}
    (a : A' ⟶ F.obj A) (b : B' ⟶ F.obj B) : A' ⊗ B' ⟶ F.obj (A ⊗ B) :=
  (a ⊗ₘ b) ≫ μ F A B

/-- 構造射とその像が、指定の二つの比較射に関して可換。 -/
def LaxComparisonSquare {A B : C} {A' B' : D}
    (a : A' ⟶ F.obj A) (b : B' ⟶ F.obj B) (f' : A' ⟶ B') (f : A ⟶ B) : Prop :=
  f' ≫ b = a ≫ F.map f

namespace LaxComparisonSquare

omit [MonoidalCategory C] [MonoidalCategory D] [F.LaxMonoidal] in
/-- 比較の恒等四角形。 -/
lemma id {A : C} {A' : D} (a : A' ⟶ F.obj A) :
    LaxComparisonSquare F a a (𝟙 A') (𝟙 A) := by
  change 𝟙 A' ≫ a = a ≫ F.map (𝟙 A)
  rw [Category.id_comp, F.map_id, Category.comp_id]

omit [MonoidalCategory C] [MonoidalCategory D] [F.LaxMonoidal] in
/-- 比較の四角形の縦合成。 -/
lemma comp {A B E : C} {A' B' E' : D}
    {a : A' ⟶ F.obj A} {b : B' ⟶ F.obj B} {c : E' ⟶ F.obj E}
    {f' : A' ⟶ B'} {g' : B' ⟶ E'} {f : A ⟶ B} {g : B ⟶ E}
    (hf : LaxComparisonSquare F a b f' f) (hg : LaxComparisonSquare F b c g' g) :
    LaxComparisonSquare F a c (f' ≫ g') (f ≫ g) := by
  unfold LaxComparisonSquare at *
  rw [Category.assoc, hg, ← Category.assoc f', hf, Category.assoc, F.map_comp]

omit [MonoidalCategory C] [MonoidalCategory D] [F.LaxMonoidal] in
/-- 比較の可逆な構造射を逆向きにたどる。 -/
lemma iso_inv {A B : C} {A' B' : D}
    {a : A' ⟶ F.obj A} {b : B' ⟶ F.obj B}
    {f' : A' ≅ B'} {f : A ≅ B} (hf : LaxComparisonSquare F a b f'.hom f.hom) :
    LaxComparisonSquare F b a f'.inv f.inv := by
  unfold LaxComparisonSquare at *
  apply (cancel_epi f'.hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc f'.hom, hf, Category.assoc,
    ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.comp_id]

/-- tensorator の自然性によって二つの比較をテンソルする。 -/
lemma tensor {A B U V : C} {A' B' U' V' : D}
    {a : A' ⟶ F.obj A} {b : B' ⟶ F.obj B} {c : U' ⟶ F.obj U} {d : V' ⟶ F.obj V}
    {f' : A' ⟶ B'} {g' : U' ⟶ V'} {f : A ⟶ B} {g : U ⟶ V}
    (hf : LaxComparisonSquare F a b f' f) (hg : LaxComparisonSquare F c d g' g) :
    LaxComparisonSquare F (laxTensorComparison F a c) (laxTensorComparison F b d)
      (f' ⊗ₘ g') (f ⊗ₘ g) := by
  unfold LaxComparisonSquare at *
  simp only [laxTensorComparison, Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, hf, hg, ← tensorHom_comp_tensorHom_assoc,
    μ_natural]

/-- 一因子を固定した左 whisker の比較。 -/
lemma whiskerLeft {A B U : C} {A' B' U' : D}
    (a : A' ⟶ F.obj A) {b : B' ⟶ F.obj B} {c : U' ⟶ F.obj U}
    {g' : B' ⟶ U'} {g : B ⟶ U} (h : LaxComparisonSquare F b c g' g) :
    LaxComparisonSquare F (laxTensorComparison F a b) (laxTensorComparison F a c)
      (A' ◁ g') (A ◁ g) := by
  simpa only [id_tensorHom] using tensor F (id F a) h

/-- 一因子を固定した右 whisker の比較。 -/
lemma whiskerRight {A B U : C} {A' B' U' : D}
    (a : A' ⟶ F.obj A) {b : B' ⟶ F.obj B} {c : U' ⟶ F.obj U}
    {g' : B' ⟶ U'} {g : B ⟶ U} (h : LaxComparisonSquare F b c g' g) :
    LaxComparisonSquare F (laxTensorComparison F b a) (laxTensorComparison F c a)
      (g' ▷ A') (g ▷ A) := by
  simpa only [tensorHom_id] using tensor F h (id F a)

/-- tensorator の結合律により、比較の括り直しは可換。 -/
lemma associator {A B E : C} {A' B' E' : D}
    (a : A' ⟶ F.obj A) (b : B' ⟶ F.obj B) (c : E' ⟶ F.obj E) :
    LaxComparisonSquare F (laxTensorComparison F (laxTensorComparison F a b) c)
      (laxTensorComparison F a (laxTensorComparison F b c))
      (α_ A' B' E').hom (α_ A B E).hom := by
  unfold LaxComparisonSquare
  simp only [laxTensorComparison, Category.assoc]
  rw [← tensorHom_comp_whiskerRight_assoc]
  exact (laxTensorator_associativity F a b c).symm

end LaxComparisonSquare

end Monoidal

namespace LaxComparisonSquare

section Braided

variable [BraidedCategory C] [BraidedCategory D] [F.LaxBraided]

/-- 係数比較は二因子の交換と可換。 -/
lemma braiding {A B : C} {A' B' : D} (a : A' ⟶ F.obj A) (b : B' ⟶ F.obj B) :
    LaxComparisonSquare F (laxTensorComparison F a b) (laxTensorComparison F b a)
      (β_ A' B').hom (β_ A B).hom := by
  unfold LaxComparisonSquare
  simp only [laxTensorComparison, Category.assoc]
  rw [Functor.LaxBraided.braided, BraidedCategory.braiding_naturality_assoc]

end Braided

end LaxComparisonSquare

end SerrePositivity.EInfinity

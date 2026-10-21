module
public import Mathlib.CategoryTheory.Monoidal.Comon_
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # 右ブロックの三つの生成操作と tensor 比較の可換性
概要：端点挿入・増大・二入力積と右端保持に関する比較を、抽象モノイダル圏で証明する。
方針：元の tensor の合成・構造同型の自然性・coherence を使う。
規約：左右の因子順を保持する。使われ方：Serre 鎖比較の右因子自然性の帰納。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- 右端への単位からの挿入は、左ブロックを分離する比較と可換。 -/
lemma monoidalRightBlock_insert {R X Y I : C} (d : R ⟶ X ⊗ Y) (e : 𝟙_ C ⟶ I) :
    (ρ_ R).inv ≫ (𝟙 R ⊗ₘ e) ≫ (d ⊗ₘ 𝟙 I) ≫ (α_ X Y I).hom =
      d ≫ (𝟙 X ⊗ₘ ((ρ_ Y).inv ≫ (𝟙 Y ⊗ₘ e))) := by
  have hx : (𝟙 R ⊗ₘ e) ≫ (d ⊗ₘ 𝟙 I) =
      (d ⊗ₘ 𝟙 (𝟙_ C)) ≫ (𝟙 (X ⊗ Y) ⊗ₘ e) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [← Category.assoc (𝟙 R ⊗ₘ e) (d ⊗ₘ 𝟙 I), hx]
  monoidal

/-- 右端の単位への削除は、左ブロックを分離する比較と可換。 -/
lemma monoidalRightBlock_delete {R X Y I : C} (d : R ⟶ X ⊗ Y) (a : I ⟶ 𝟙_ C) :
    (𝟙 R ⊗ₘ a) ≫ (ρ_ R).hom ≫ d =
      (d ⊗ₘ 𝟙 I) ≫ (α_ X Y I).hom ≫ (𝟙 X ⊗ₘ ((𝟙 Y ⊗ₘ a) ≫ (ρ_ Y).hom)) := by
  rw [← rightUnitor_naturality d]
  have hx : (𝟙 R ⊗ₘ a) ≫ (d ⊗ₘ 𝟙 (𝟙_ C)) =
      (d ⊗ₘ 𝟙 I) ≫ (𝟙 (X ⊗ Y) ⊗ₘ a) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [← tensorHom_id, ← Category.assoc, hx]
  monoidal

/-- 右端の二入力積は、同じ二段の左ブロック比較と可換。 -/
lemma monoidalRightBlock_multiply {R X Y I : C} (d : R ⟶ X ⊗ Y) (m : I ⊗ I ⟶ I) :
    (α_ R I I).hom ≫ (𝟙 R ⊗ₘ m) ≫ (d ⊗ₘ 𝟙 I) ≫ (α_ X Y I).hom =
      (((d ⊗ₘ 𝟙 I) ≫ (α_ X Y I).hom) ⊗ₘ 𝟙 I) ≫
        (α_ X (Y ⊗ I) I).hom ≫ (𝟙 X ⊗ₘ ((α_ Y I I).hom ≫ (𝟙 Y ⊗ₘ m))) := by
  have hx : (𝟙 R ⊗ₘ m) ≫ (d ⊗ₘ 𝟙 I) =
      (d ⊗ₘ 𝟙 (I ⊗ I)) ≫ (𝟙 (X ⊗ Y) ⊗ₘ m) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [← Category.assoc (𝟙 R ⊗ₘ m) (d ⊗ₘ 𝟙 I), hx]
  monoidal

/-- 元の二つの比較を括弧つきのまま保つ、右端二入力積の可換性。 -/
lemma monoidalRightBlock_multiply_comparison {R X Y I : C}
    (d : R ⟶ X ⊗ Y) (m : I ⊗ I ⟶ I) :
    ((α_ R I I).hom ≫ (𝟙 R ⊗ₘ m)) ≫ ((d ⊗ₘ 𝟙 I) ≫ (α_ X Y I).hom) =
      ((((d ⊗ₘ 𝟙 I) ≫ (α_ X Y I).hom) ⊗ₘ 𝟙 I) ≫ (α_ X (Y ⊗ I) I).hom) ≫
        (𝟙 X ⊗ₘ ((α_ Y I I).hom ≫ (𝟙 Y ⊗ₘ m))) := by
  simpa only [Category.assoc] using monoidalRightBlock_multiply d m

/-- 元の同型を展開せずに保持した、右端の二入力積の可換性。 -/
lemma monoidalRightBlock_multiply_iso {R X Y I : C}
    (d : R ≅ X ⊗ Y) (m : I ⊗ I ⟶ I) :
    ((α_ R I I).hom ≫ (𝟙 R ⊗ₘ m)) ≫
        ((d ⊗ᵢ Iso.refl I) ≪≫ α_ X Y I).hom =
      ((((d ⊗ᵢ Iso.refl I) ≪≫ α_ X Y I) ⊗ᵢ Iso.refl I) ≪≫ α_ X (Y ⊗ I) I).hom ≫
        (𝟙 X ⊗ₘ ((α_ Y I I).hom ≫ (𝟙 Y ⊗ₘ m))) := by
  simpa only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom] using
    monoidalRightBlock_multiply_comparison d.hom m

/-- 右因子の元の可換四角形を、右端を一つ保持した比較へ移す。 -/
lemma monoidalRightBlock_keep {R S X Y Z I : C} (d : R ⟶ X ⊗ Y) (e : S ⟶ X ⊗ Z)
    (h : R ⟶ S) (f : Y ⟶ Z) (hf : h ≫ e = d ≫ (𝟙 X ⊗ₘ f)) :
    (h ⊗ₘ 𝟙 I) ≫ (e ⊗ₘ 𝟙 I) ≫ (α_ X Z I).hom =
      (d ⊗ₘ 𝟙 I) ≫ (α_ X Y I).hom ≫ (𝟙 X ⊗ₘ (f ⊗ₘ 𝟙 I)) := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, hf]
  monoidal

/-- 元の比較の括弧を保った、右端保持の帰納段階。 -/
lemma monoidalRightBlock_keep_comparison {R S X Y Z I : C}
    (d : R ⟶ X ⊗ Y) (e : S ⟶ X ⊗ Z) (h : R ⟶ S) (f : Y ⟶ Z)
    (hf : h ≫ e = d ≫ (𝟙 X ⊗ₘ f)) :
    (h ⊗ₘ 𝟙 I) ≫ ((e ⊗ₘ 𝟙 I) ≫ (α_ X Z I).hom) =
      ((d ⊗ₘ 𝟙 I) ≫ (α_ X Y I).hom) ≫ (𝟙 X ⊗ₘ (f ⊗ₘ 𝟙 I)) := by
  simpa only [Category.assoc] using monoidalRightBlock_keep d e h f hf

/-- 右ブロックの二つの元の可換四角形の合成。 -/
lemma monoidalRightBlock_comp {R S T X Y Z W : C}
    (d : R ⟶ X ⊗ Y) (e : S ⟶ X ⊗ Z) (v : T ⟶ X ⊗ W)
    (h : R ⟶ S) (i : S ⟶ T) (f : Y ⟶ Z) (g : Z ⟶ W)
    (hh : h ≫ e = d ≫ (𝟙 X ⊗ₘ f)) (hi : i ≫ v = e ≫ (𝟙 X ⊗ₘ g)) :
    (h ≫ i) ≫ v = d ≫ (𝟙 X ⊗ₘ (f ≫ g)) := by
  rw [Category.assoc, hi, ← Category.assoc, hh, Category.assoc,
    tensorHom_comp_tensorHom, Category.id_comp]

/-- 元の左ブロックと右ブロックの可換四角形の合成。 -/
lemma monoidalBlocks_paste {R S T X X' Y Y' : C}
    (d : R ⟶ X ⊗ Y) (e : S ⟶ X' ⊗ Y) (v : T ⟶ X' ⊗ Y')
    (h : R ⟶ S) (i : S ⟶ T) (f : X ⟶ X') (g : Y ⟶ Y')
    (hh : h ≫ e = d ≫ (f ⊗ₘ 𝟙 Y)) (hi : i ≫ v = e ≫ (𝟙 X' ⊗ₘ g)) :
    (h ≫ i) ≫ v = d ≫ (f ⊗ₘ g) := by
  rw [Category.assoc, hi, ← Category.assoc, hh, Category.assoc,
    tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

end SerrePositivity.KST.SConstruction

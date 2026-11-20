module


public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
概要：豊穣合成における中間の射の前合成と後合成の一致。
方針：豊穣結合律とモノイダル圏の三角恒等式を使う。
規約：任意の通常の豊穣圏に対する一般の圏論。
使われ方：HTT A.3.3、BF 1978 §2。スペクトルの合成の境界整合性。
-/

@[expose] public section

universe v w u z

open CategoryTheory MonoidalCategory

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra

variable (V : Type u) [Category.{v} V] [MonoidalCategory V]
  {C : Type z} [Category.{w} C] [EnrichedOrdinaryCategory V C]

/-- 概要：中間の通常の射を豊穣合成の左右どちらに作用させても一致する。
方針：豊穣結合律と左右の単位の整合性を使う。
規約：中間の射は同型である必要はない。
使われ方：HTT A.3.3、BF 1978 §2。段の構造射を合成の間で移す。 -/
@[reassoc]
theorem enriched_comp_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    eHomWhiskerLeft V X f ▷ (Y' ⟶[V] Z) ≫ eComp V X Y' Z =
      (X ⟶[V] Y) ◁ eHomWhiskerRight V f Z ≫ eComp V X Y Z := by
  dsimp only [eHomWhiskerLeft, eHomWhiskerRight]
  simp only [comp_whiskerRight_assoc, whiskerLeft_comp_assoc]
  rw [← e_assoc, associator_inv_naturality_middle_assoc]
  simp

/-- 概要：豊穣関手の構造射と整合する二つの写像族の合成も整合する。
方針：前合成・後合成の自然性、中間の射の移動、豊穣関手の合成保存を使う。
規約：任意のパラメータ対象 P と Q。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの単体的合成を極限へ持ち上げる条件。 -/
theorem enriched_compatible_comp (F : EnrichedFunctor V C C)
    {X Y Z X' Y' Z' : C} (sx : F.obj X ⟶ X') (sy : F.obj Y ⟶ Y') (sz : F.obj Z ⟶ Z')
    {P Q : V} (a : P ⟶ (X ⟶[V] Y)) (a' : P ⟶ (X' ⟶[V] Y'))
    (b : Q ⟶ (Y ⟶[V] Z)) (b' : Q ⟶ (Y' ⟶[V] Z'))
    (ha : a' ≫ eHomWhiskerRight V sx Y' = a ≫ F.map X Y ≫ eHomWhiskerLeft V (F.obj X) sy)
    (hb : b' ≫ eHomWhiskerRight V sy Z' = b ≫ F.map Y Z ≫ eHomWhiskerLeft V (F.obj Y) sz) :
    (a' ⊗ₘ b') ≫ eComp V X' Y' Z' ≫ eHomWhiskerRight V sx Z' =
      (a ⊗ₘ b) ≫ eComp V X Y Z ≫ F.map X Z ≫ eHomWhiskerLeft V (F.obj X) sz := by
  rw [eComp_eHomWhiskerRight, ← Category.assoc, tensorHom_comp_whiskerRight, ha]
  rw [← Category.assoc a (F.map X Y)]
  rw [← tensorHom_comp_whiskerRight (a ≫ F.map X Y)
    (eHomWhiskerLeft V (F.obj X) sy) b', Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_comp_middle]
  rw [← Category.assoc, tensorHom_comp_whiskerLeft, hb]
  rw [← Category.assoc b (F.map Y Z)]
  rw [← tensorHom_comp_whiskerLeft (a ≫ F.map X Y) (b ≫ F.map Y Z)
    (eHomWhiskerLeft V (F.obj Y) sz), Category.assoc, ← eComp_eHomWhiskerLeft]
  rw [← tensorHom_comp_tensorHom, Category.assoc, ← EnrichedFunctor.map_comp_assoc]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

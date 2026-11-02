module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Monoidal.Braided

## 概要
関連する圏論の構成と補題をまとめる。各構成の詳細は以下の元モジュールの説明を参照。

## 方針
元の宣言と証明を保持し、依存順に section を分けて配置する。

## 規約
公開宣言名・名前空間・宇宙変数の意味を変更しない。元の module docstring は各節に保存する。

## 使われ方
旧モジュールの利用元は `SerrePositivity.CategoryTheory.Monoidal.Braided` を直接 import する。
-/

/-! ## BraidingPreservation（旧 SerrePositivity/CategoryTheory/Monoidal/BraidingPreservation.lean） -/

/-! # モノイダル関手のbraidingの保存をテンソル積へ拡張する

二つの対象と固定された第三の対象とのbraidingを保存する場合、
その二対象のテンソル積と第三の対象とのbraidingも保存する。
hexagonとモノイダル関手の整合性を使う、スペクトルに依存しない一般論。
-/

@[expose] public section BraidingPreservation
universe v u v' u'

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalFunctor

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal
  CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D] [BraidedCategory D]

/-- 二つの対象とのbraidingの保存から、そのテンソル積とのbraidingの保存を得る。 -/
lemma map_braiding_tensor_left (F : C ⥤ D) [F.Monoidal] (X Y Z : C)
    (hx : F.map (β_ X Z).hom = δ F X Z ≫ (β_ (F.obj X) (F.obj Z)).hom ≫ μ F Z X)
    (hy : F.map (β_ Y Z).hom = δ F Y Z ≫ (β_ (F.obj Y) (F.obj Z)).hom ≫ μ F Z Y) :
    F.map (β_ (X ⊗ Y) Z).hom =
      δ F (X ⊗ Y) Z ≫ (β_ (F.obj (X ⊗ Y)) (F.obj Z)).hom ≫ μ F Z (X ⊗ Y) := by
  rw [braiding_tensor_left_hom]
  simp only [CategoryTheory.Functor.map_comp, map_associator, map_associator_inv,
    map_whiskerLeft, map_whiskerRight, hx, hy, MonoidalCategory.whiskerLeft_comp, comp_whiskerRight,
    Category.assoc]
  simp only [μ_δ_assoc, whiskerLeft_μ_δ_assoc, whiskerRight_μ_δ_assoc]
  rw [← braiding_tensor_left_hom_assoc, braiding_naturality_left_assoc]
  simp

end SerrePositivity.MonoidalFunctor

end BraidingPreservation

/-! ## InternalHomExchange（旧 SerrePositivity/CategoryTheory/Monoidal/InternalHomExchange.lean） -/

/-! # Exchanging the two variables of an iterated internal Hom

The isomorphism uses actual internal currying and the braiding. Its double
uncurry formula records the two evaluations explicitly for model-theoretic
applications; no model structure is involved here.
-/

@[expose] public section InternalHomExchange
universe v u

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.InternalHomExchange
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C]

def iso (X K Z : C) : (ihom X).obj ((ihom K).obj Z) ≅ (ihom K).obj ((ihom X).obj Z) :=
  (ihomCurryIso K X Z).symm ≪≫
    (MonoidalClosed.internalHom.mapIso (β_ X K).op).app Z ≪≫ ihomCurryIso X K Z

omit [BraidedCategory C] in
lemma doubleUncurry_comp_ihomCurry (X K Z A : C) (f : A ⟶ (ihom (X ⊗ K)).obj Z) :
    uncurry (uncurry (f ≫ ihomCurry X K Z)) = (α_ X K A).inv ≫ uncurry f := by
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_uncurry_ihomCurry,
    associator_inv_naturality_right_assoc]
  rw [uncurry_eq]

lemma doubleUncurry_iso_hom (X K Z : C) :
    uncurry (uncurry (iso X K Z).hom) =
      (α_ X K ((ihom X).obj ((ihom K).obj Z))).inv ≫
        (β_ X K).hom ▷ (ihom X).obj ((ihom K).obj Z) ≫
          (α_ K X ((ihom X).obj ((ihom K).obj Z))).hom ≫
            K ◁ (ihom.ev X).app ((ihom K).obj Z) ≫ (ihom.ev K).app Z := by
  change uncurry (uncurry
    (ihomUncurry K X Z ≫ (pre (β_ X K).hom).app Z ≫ ihomCurry X K Z)) = _
  rw [← Category.assoc, doubleUncurry_comp_ihomCurry, uncurry_pre_app, uncurry_ihomUncurry]

lemma doubleUncurry_map_exchange (X K Z Y : C) (f : Y ⟶ (ihom K).obj Z) :
    uncurry (uncurry ((ihom X).map f ≫ (iso X K Z).hom)) =
      (α_ X K ((ihom X).obj Y)).inv ≫
        (β_ X K).hom ▷ (ihom X).obj Y ≫
          (α_ K X ((ihom X).obj Y)).hom ≫ K ◁ (ihom.ev X).app Y ≫ uncurry f := by
  rw [uncurry_natural_left, uncurry_natural_left, doubleUncurry_iso_hom,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc]
  have hn : X ◁ (ihom X).map f ≫ (ihom.ev X).app ((ihom K).obj Z) =
      (ihom.ev X).app Y ≫ f := (ihom.ev X).naturality f
  rw [← whiskerLeft_comp_assoc, hn, whiskerLeft_comp, Category.assoc, uncurry_eq]

end SerrePositivity.InternalHomExchange
end

end InternalHomExchange

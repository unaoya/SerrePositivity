module

public import SerrePositivity.CategoryTheory.Quiver.FreePathComonad
public import Mathlib.CategoryTheory.NatIso

/-!
# 対象の移送後の単一辺の道を余単位で評価すると元の辺の移送に一致する

## 概要
対象の移送後の単一辺の道を余単位で評価すると元の辺の移送に一致する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
生成辺と空の道を指定し、道の長さに関する帰納で射を比較する。
連結との交換から関手または自然変換の法則を確認する。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0036][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0036
[plan]: ../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Singleton paths commute with exact object transports
-/

@[expose] public section
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.QuiverPaths
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

lemma singleton_transport {X X' Y Y' : D} (hX : X' = X) (hY : Y = Y') (f : X ⟶ Y) :
    Quiver.Path.comp (@eqToHom (Paths D) (Paths.categoryPaths D).toCategoryStruct X' X hX)
      (Quiver.Path.comp f.toPath
        (@eqToHom (Paths D) (Paths.categoryPaths D).toCategoryStruct Y Y' hY)) =
        (eqToHom hX ≫ f ≫ eqToHom hY).toPath := by
  cases hX
  cases hY
  change Quiver.Path.comp Quiver.Path.nil (Quiver.Path.comp f.toPath Quiver.Path.nil) =
    (𝟙 X ≫ f ≫ 𝟙 Y).toPath
  simp only [Quiver.Path.nil_comp, Quiver.Path.comp_nil, Category.id_comp, Category.comp_id]

lemma map_copyObj_generator (F : C ⥤ D) (g : C → D) (h : ∀ X, F.obj X = g X)
    {X Y : C} (f : X ⟶ Y) :
    ((HomotopyFunctionComplex.FreePathResolution.map F).copyObj (fun X => g X)
      (fun X => eqToIso (h X))).map f.toPath =
        ((F.copyObj g (fun X => eqToIso (h X))).map f).toPath := by
  change Quiver.Path.comp
      (@eqToHom (Paths D) (Paths.categoryPaths D).toCategoryStruct (g X) (F.obj X) (h X).symm)
      (Quiver.Path.comp (F.map f).toPath
        (@eqToHom (Paths D) (Paths.categoryPaths D).toCategoryStruct (F.obj Y) (g Y) (h Y))) = _
  exact singleton_transport (h X).symm (h Y) (F.map f)

/-- 対象の移送後の単一辺の道を余単位で評価すると元の辺の移送に一致する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
生成辺と空の道を指定し、道の長さに関する帰納で射を比較する。
連結との交換から関手または自然変換の法則を確認する。
-/
lemma counit_copy_singleton {X Y : D} (f : X ⟶ Y) :
    ((HomotopyFunctionComplex.FreePathResolution.counit D).copyObj (fun X => (X : D))
      (fun X => @Iso.refl.{v', u'} D inferInstance X)).map f.toPath = f := by
  simp only [Functor.copyObj, Iso.refl_inv, Iso.refl_hom, Category.id_comp]
  exact (@Category.comp_id D inferInstance X Y
    ((HomotopyFunctionComplex.FreePathResolution.counit D).map f.toPath)).trans
      (composePath_toPath f)

end SerrePositivity.QuiverPaths

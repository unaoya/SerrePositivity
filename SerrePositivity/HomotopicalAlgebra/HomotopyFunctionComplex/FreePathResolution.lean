module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Monad.Basic

/-!
# 中断した任意モデル源への一般化：FreePathResolution

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The free-path comonad, with explicit generators and all three laws。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0098][inventory]を参照する。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0098
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The free-path comonad, with explicit generators and all three laws

The generic formulas allow independent object and Hom universes. They
provide the counit and duplication operations used in free resolutions;
no model category, enrichment, or infinite-category construction is used.
-/

@[expose] public section
universe u v u' v' u'' v''
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.HomotopyFunctionComplex.FreePathResolution
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]

def map (F : C ⥤ D) : Paths C ⥤ Paths D where
  obj X := F.obj X
  map p := F.toPrefunctor.mapPath p
  map_id _ := rfl
  map_comp p q := Prefunctor.mapPath_comp _ p q

lemma map_generator (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    (map F).map f.toPath = (F.map f).toPath := rfl

lemma map_id : map (𝟭 C) = 𝟭 (Paths C) := by
  refine Paths.ext_functor (F := map (𝟭 C)) (G := 𝟭 (Paths C)) rfl ?_
  intro X Y f
  rfl

lemma map_comp (F : C ⥤ D) (G : D ⥤ E) : map (F ⋙ G) = map F ⋙ map G := by
  refine Paths.ext_functor (F := map (F ⋙ G)) (G := map F ⋙ map G) rfl ?_
  intro X Y f
  rfl

abbrev counit (C : Type u) [Category.{v} C] : Paths C ⥤ C := pathComposition C

lemma lift_identity : Paths.lift (𝟭q C) = counit C := by
  refine Paths.ext_functor (F := Paths.lift (𝟭q C)) (G := counit C) rfl ?_
  intro X Y f
  simp only [Paths.lift_toPath, Prefunctor.id_map, counit, pathComposition_map,
    composePath_toPath, eqToHom_refl, Category.id_comp, Category.comp_id]

def duplicateGenerators (C : Type u) [Category.{v} C] : C ⥤q Paths (Paths C) where
  obj X := X
  map f := Quiver.Hom.toPath (V := Paths C) f.toPath

def duplicate (C : Type u) [Category.{v} C] : Paths C ⥤ Paths (Paths C) :=
  Paths.lift (duplicateGenerators C)

lemma duplicate_generator {X Y : C} (f : X ⟶ Y) :
    (duplicate C).map f.toPath = Quiver.Hom.toPath (V := Paths C) f.toPath :=
  Paths.lift_toPath _ f

lemma counit_naturality (F : C ⥤ D) : map F ⋙ counit D = counit C ⋙ F := by
  refine Paths.ext_functor (F := map F ⋙ counit D) (G := counit C ⋙ F) rfl ?_
  intro X Y f
  simp only [CategoryTheory.Functor.comp_map, map_generator, counit, pathComposition_map,
    composePath_toPath, eqToHom_refl, Category.id_comp, Category.comp_id]

lemma duplicate_naturality (F : C ⥤ D) :
    map F ⋙ duplicate D = duplicate C ⋙ map (map F) := by
  refine Paths.ext_functor (F := map F ⋙ duplicate D) (G := duplicate C ⋙ map (map F)) rfl ?_
  intro X Y f
  simp only [CategoryTheory.Functor.comp_map, map_generator, duplicate_generator,
    eqToHom_refl, Category.id_comp, Category.comp_id]

lemma left_counit : duplicate C ⋙ counit (Paths C) = 𝟭 (Paths C) := by
  refine Paths.ext_functor (F := duplicate C ⋙ counit (Paths C)) (G := 𝟭 (Paths C)) rfl ?_
  intro X Y f
  simp only [CategoryTheory.Functor.comp_map, duplicate_generator, counit, pathComposition_map,
    composePath_toPath, CategoryTheory.Functor.id_map, eqToHom_refl,
    Category.id_comp, Category.comp_id]

lemma right_counit : duplicate C ⋙ map (counit C) = 𝟭 (Paths C) := by
  refine Paths.ext_functor (F := duplicate C ⋙ map (counit C)) (G := 𝟭 (Paths C)) rfl ?_
  intro X Y f
  simp only [CategoryTheory.Functor.comp_map, duplicate_generator, map_generator, counit,
    pathComposition_map, composePath_toPath, CategoryTheory.Functor.id_map,
    eqToHom_refl, Category.id_comp, Category.comp_id]

lemma coassociativity : duplicate C ⋙ map (duplicate C) = duplicate C ⋙ duplicate (Paths C) := by
  refine Paths.ext_functor
    (F := duplicate C ⋙ map (duplicate C)) (G := duplicate C ⋙ duplicate (Paths C)) rfl ?_
  intro X Y f
  simp only [CategoryTheory.Functor.comp_map, duplicate_generator, map_generator,
    eqToHom_refl, Category.id_comp, Category.comp_id]

def endofunctor : Cat.{max u v, u} ⥤ Cat.{max u v, u} where
  obj C := Cat.of (Paths C)
  map F := (map F.toFunctor).toCatHom
  map_id _ := by
    apply Cat.ext
    exact map_id
  map_comp F G := by
    apply Cat.ext
    exact map_comp F.toFunctor G.toFunctor

def counitNatTrans : endofunctor.{u, v} ⟶ 𝟭 _ where
  app C := (counit C).toCatHom
  naturality {_ _} F := by
    apply Cat.ext
    exact counit_naturality F.toFunctor

def duplicateNatTrans : endofunctor.{u, v} ⟶ endofunctor ⋙ endofunctor where
  app C := (duplicate C).toCatHom
  naturality {_ _} F := by
    apply Cat.ext
    exact duplicate_naturality F.toFunctor

def comonad : Comonad Cat.{max u v, u} where
  toFunctor := endofunctor
  ε := counitNatTrans
  δ := duplicateNatTrans
  coassoc C := by apply Cat.ext; exact coassociativity (C := C)
  left_counit C := by apply Cat.ext; exact left_counit (C := C)
  right_counit C := by apply Cat.ext; exact right_counit (C := C)

end SerrePositivity.HomotopyFunctionComplex.FreePathResolution

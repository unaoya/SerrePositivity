module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths

/-!
# 指定生成矢とその補集合による自由圏の貼り合わせ

概要：元の Paths C からの関手を、指定生成矢と非指定生成矢の自由圏から貼り合わせる。
方針：元の各生成矢を所属判定で分け、自由圏の普遍性で全射列へ拡張する。
規約：両関手の対象表示の等式を移送に使い、元の生成矢を削除しない。
使われ方：Dwyer–Kan 比較補題2.3の元の自由積分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {D : Type u'} [Category.{v'} D]

def unmarked : MorphismProperty C := fun _ _ f => ¬ W f

variable (F : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver W) ⥤ D)
  (G : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.quiver (unmarked W)) ⥤ D)
  (h : ∀ X : C, F.obj X = G.obj X)

def extendPrefunctor : C ⥤q D where
  obj X := F.obj X
  map {X Y} f := by
    classical
    exact if hf : W f then F.map (Quiver.Hom.toPath ⟨f, hf⟩)
      else eqToHom (h X) ≫ G.map (Quiver.Hom.toPath ⟨f, hf⟩) ≫ eqToHom (h Y).symm

def extendFunctor : Paths C ⥤ D := Paths.lift (extendPrefunctor W F G h)

lemma extend_marked {X Y : C} (f : X ⟶ Y) (hf : W f) :
    (extendFunctor W F G h).map f.toPath = F.map (Quiver.Hom.toPath ⟨f, hf⟩) := by
  classical
  simp only [extendFunctor, Paths.lift_toPath, extendPrefunctor, dite_eq_left hf]

lemma extend_unmarked {X Y : C} (f : X ⟶ Y) (hf : ¬ W f) :
    (extendFunctor W F G h).map f.toPath =
      eqToHom (h X) ≫ G.map (Quiver.Hom.toPath ⟨f, hf⟩) ≫ eqToHom (h Y).symm := by
  classical
  simp only [extendFunctor, Paths.lift_toPath, extendPrefunctor, dite_eq_right hf]

lemma marked_fac : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W ⋙ extendFunctor W F G h = F := by
  apply Paths.ext_functor (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion W ⋙ extendFunctor W F G h)
    (G := F) (funext (fun _ => rfl))
  intro X Y f
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  change (extendFunctor W F G h).map f.val.toPath = F.map f.toPath
  exact extend_marked W F G h f.val f.property

lemma unmarked_fac :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion (unmarked W) ⋙ extendFunctor W F G h = G := by
  apply Paths.ext_functor
    (F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MarkedGeneratorPaths.inclusion (unmarked W) ⋙ extendFunctor W F G h)
    (G := G) (funext h)
  intro X Y f
  change (extendFunctor W F G h).map f.val.toPath =
    eqToHom (h X) ≫ G.map f.toPath ≫ eqToHom (h Y).symm
  exact extend_unmarked W F G h f.val f.property

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroLocalization

/-!
# 元の anodyne 局所化内の比較が誘導する連結成分の写像

概要：π₀ を同じ局所化へ降ろし、元の全比較射へ作用させる。
方針：π₀ が元の anodyne 射を反転する定理と局所化の因子化同型を使う。
規約：元の実単体写像には通常の mapπ₀ を厳密に回収する。
使われ方：既存の DK/Map^h 比較と以前の π₀ 同値との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents
open _root_.CategoryTheory _root_.SerrePositivity.SimplicialModel

abbrev componentsFunctor := Localization.lift SSet.π₀Functor.{u}
  PiZeroLocalization.inverts_anodyne AnodyneHomotopy.anodyneQ

def componentsFactorization : AnodyneHomotopy.anodyneQ ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.componentsFunctor ≅ SSet.π₀Functor.{u} :=
  Localization.fac SSet.π₀Functor PiZeroLocalization.inverts_anodyne AnodyneHomotopy.anodyneQ

variable {X Y Z : SSet.{u}}

def map (f : AnodyneHomotopy.anodyneQ.obj X ⟶ AnodyneHomotopy.anodyneQ.obj Y) :
    SSet.π₀ X ⟶ SSet.π₀ Y :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.componentsFactorization.app X).inv ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.componentsFunctor.map f ≫
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.componentsFactorization.app Y).hom

lemma map_comp (f : AnodyneHomotopy.anodyneQ.obj X ⟶ AnodyneHomotopy.anodyneQ.obj Y)
    (g : AnodyneHomotopy.anodyneQ.obj Y ⟶ AnodyneHomotopy.anodyneQ.obj Z) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.map (f ≫ g) = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.map f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.map g := by
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.map, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

lemma map_actual (f : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.map (AnodyneHomotopy.anodyneQ.map f) = SSet.π₀Functor.map f := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.componentsFactorization.hom.naturality f
  change _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.componentsFunctor.map (AnodyneHomotopy.anodyneQ.map f) ≫
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.componentsFactorization.app Y).hom =
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.componentsFactorization.app X).hom ≫ SSet.π₀Functor.map f at h
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.map]
  rw [h, Iso.inv_hom_id_assoc]

def iso (e : AnodyneHomotopy.anodyneQ.obj X ≅ AnodyneHomotopy.anodyneQ.obj Y) :
    SSet.π₀ X ≅ SSet.π₀ Y :=
  (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.componentsFactorization.app X).symm ≪≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.componentsFunctor.mapIso e ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.componentsFactorization.app Y

lemma iso_hom (e : AnodyneHomotopy.anodyneQ.obj X ≅ AnodyneHomotopy.anodyneQ.obj Y) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.iso e).hom = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.map e.hom := rfl

lemma iso_fac {T : SSet.{u}}
    (e : AnodyneHomotopy.anodyneQ.obj X ≅ AnodyneHomotopy.anodyneQ.obj Y)
    (l : T ⟶ X) (r : T ⟶ Y)
    (h : AnodyneHomotopy.anodyneQ.map l ≫ e.hom = AnodyneHomotopy.anodyneQ.map r) :
    SSet.π₀Functor.map l ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.iso e).hom = SSet.π₀Functor.map r := by
  have he := congrArg _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.map h
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.map_comp, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.map_actual, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.iso_hom] using he

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents

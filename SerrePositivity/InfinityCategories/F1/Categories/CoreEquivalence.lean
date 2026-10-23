module

public import SerrePositivity.InfinityCategories.F1.Categories.CoreFunctorIso

/-!
概要：quasicategory の同値は元の core の間でも同値。
方針：元の逆射と二つの関手同型を core 関手で移す。
規約：順方向は既存の quasicategoryCoreMap に固定する。
使われ方：cocartesian strict transport の局所同値性を core の豊穣 Hom へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の quasicategory の同値から、同じ core 写像を順方向とする同値を構成する。 -/
def QCatEquivalence.core {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : QCatEquivalence X Y) :
    QCatEquivalence (quasicategoryCore X : SSet.{u}) (quasicategoryCore Y : SSet.{u}) where
  hom := quasicategoryCoreMap e.hom
  inv := quasicategoryCoreMap e.inv
  homInvIso := by
    have h := e.homInvIso.core
    change FunctorIso (quasicategoryCoreFunctor.map (e.hom ≫ e.inv))
      (quasicategoryCoreFunctor.map (𝟙 X)) at h
    change FunctorIso (quasicategoryCoreFunctor.map e.hom ≫ quasicategoryCoreFunctor.map e.inv)
      (𝟙 (quasicategoryCoreFunctor.obj X))
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using h
  invHomIso := by
    have h := e.invHomIso.core
    change FunctorIso (quasicategoryCoreFunctor.map (e.inv ≫ e.hom))
      (quasicategoryCoreFunctor.map (𝟙 Y)) at h
    change FunctorIso (quasicategoryCoreFunctor.map e.inv ≫ quasicategoryCoreFunctor.map e.hom)
      (𝟙 (quasicategoryCoreFunctor.obj Y))
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using h

/-- 同値な元の射の core 写像そのものは quasicategory の同値。 -/
lemma IsQCatEquivalence.core {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : IsQCatEquivalence f) : IsQCatEquivalence (quasicategoryCoreMap f) :=
  hf.choose.core.isQCatEquivalence

end SerrePositivity.InfinityCategories

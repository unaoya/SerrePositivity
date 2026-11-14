module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：内部 Hom の各単体の宇宙移送と厳密な往復。
方針：各入力の ULift を外して元の評価を行い、出力を持ち上げる。
規約：元のパラメーターの単体を変えない。既存の深層モジュールは不変。
使われ方：局所化の全関手圏の宇宙比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

def uliftFunctorHomUp {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (f : ((ihom A).obj E).obj n) :
    ((ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj ((SSet.uliftFunctor.{v, u}).obj E)).obj n where
  app d α := ↾fun x => ULift.up (f.app d α x.down)
  naturality g α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact ConcreteCategory.congr_hom (f.naturality g α) x.down

def uliftFunctorHomDown {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (f : ((ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj
      ((SSet.uliftFunctor.{v, u}).obj E)).obj n) : ((ihom A).obj E).obj n where
  app d α := ↾fun x => (f.app d α (ULift.up x)).down
  naturality {c d} g α := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun (k : ((SSet.uliftFunctor.{v, u}).obj A).obj c ⟶
      ((SSet.uliftFunctor.{v, u}).obj E).obj d) => (k (ULift.up.{v, u} x)).down)
        (f.naturality g α)

lemma uliftFunctorHomDown_up {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (f : ((ihom A).obj E).obj n) :
    uliftFunctorHomDown (uliftFunctorHomUp.{u, v} f) = f := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

lemma uliftFunctorHomUp_down {A E : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (f : ((ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj
      ((SSet.uliftFunctor.{v, u}).obj E)).obj n) :
    uliftFunctorHomUp (uliftFunctorHomDown f) = f := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

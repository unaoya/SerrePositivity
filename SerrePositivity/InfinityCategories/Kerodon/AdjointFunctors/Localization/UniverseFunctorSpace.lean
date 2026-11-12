module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseFunctorSpaceData

/-!
概要：全関手圏の厳密な宇宙同型と元の前合成の可換性。
方針：各次数の元の評価を保つ往復を射に組み立てる。
規約：quasicategory 性を使わない。同じ全射の等式を保つ。
使われ方：持ち上げた局所化の全前合成を元の宇宙へ戻す。

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

def uliftFunctorSpaceMap (A E : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj ((ihom A).obj E) ⟶
      (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj ((SSet.uliftFunctor.{v, u}).obj E) where
  app n := ↾fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftFunctorHomUp f.down
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro f
    apply CategoryTheory.Functor.functorHom_ext
    intro k γ
    rfl

def uliftFunctorSpaceDown (A E : SSet.{u}) :
    (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj ((SSet.uliftFunctor.{v, u}).obj E) ⟶
      (SSet.uliftFunctor.{v, u}).obj ((ihom A).obj E) where
  app n := ↾fun f => ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftFunctorHomDown f)
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    apply CategoryTheory.Functor.functorHom_ext
    intro k γ
    rfl

def uliftFunctorSpaceIso (A E : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).obj ((ihom A).obj E) ≅
      (ihom ((SSet.uliftFunctor.{v, u}).obj A)).obj ((SSet.uliftFunctor.{v, u}).obj E) where
  hom := uliftFunctorSpaceMap A E
  inv := uliftFunctorSpaceDown A E
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftFunctorHomDown_up.{u, v} f.down
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.uliftFunctorHomUp_down.{u, v} f

lemma uliftFunctorSpaceIso_pre {X D : SSet.{u}} (F : X ⟶ D) (E : SSet.{u}) :
    (SSet.uliftFunctor.{v, u}).map ((pre F).app E) ≫ (uliftFunctorSpaceIso X E).hom =
      (uliftFunctorSpaceIso D E).hom ≫
        (pre ((SSet.uliftFunctor.{v, u}).map F)).app (SSet.uliftFunctor.{v, u}.obj E) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

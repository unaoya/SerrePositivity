module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram

/-!
概要：全 Hom に自然な quasicategory 値豊穣関手の比較を、底全体の図式へ束ねる。
方針：各対象の元の図式と、全高次 Hom の各成分の作用を保持する。
規約：値や全変換空間の Kan 性を要求しない。
使われ方：底変換比較を底の全対象・全射で同時に実現する入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 概要：豊穣比較の図式は通常の Kan 図式を値とする一つの豊穣関手。
方針：成分ごとの単位則・合成則を strict 変換空間で同時に使う。
規約：任意の添字圏を扱い、二点図式の場合も含む。
使われ方：全対象を同時に動かす比較の列の coherent な実現。 -/
def QuasicategoryEnrichedDiagram.toEnrichedFunctor {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedDiagram C J) :
    EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryDiagramObject J) where
  obj X := ⟨D.evaluate X, trivial⟩
  map := D.mappingSpaceMap
  map_id X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    funext j
    exact congrArg (fun f : 𝟙_ SSet.{u} ⟶
      (ihom ((D.obj j).obj X).obj).obj ((D.obj j).obj X).obj ↦ f.app n t)
      ((D.obj j).map_id X)
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply Subtype.ext
    funext j
    have h := congrArg (fun m : SimplicialCategory.sHom X Y ⊗ SimplicialCategory.sHom Y Z ⟶
      (ihom ((D.obj j).obj X).obj).obj ((D.obj j).obj Z).obj ↦ m.app n (f, g))
      ((D.obj j).map_comp X Y Z)
    apply CategoryTheory.Functor.functorHom_ext
    intro k α
    apply ConcreteCategory.hom_ext
    intro x
    have h' := congrArg (fun θ :
      ((ihom ((D.obj j).obj X).obj).obj ((D.obj j).obj Z).obj).obj n ↦ θ.app k α x) h
    change (((D.obj j).map X Z).app n ((eComp SSet X Y Z).app n (f, g))).app k α x =
      (((D.obj j).map Y Z).app n g).app k (α ≫ 𝟙 k)
        ((((D.obj j).map X Y).app n f).app k (α ≫ 𝟙 k) x) at h'
    rw [Category.comp_id] at h'
    exact h'

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

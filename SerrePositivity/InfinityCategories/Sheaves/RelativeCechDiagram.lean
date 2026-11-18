module

public import SerrePositivity.CategoryTheory.CechNerveFiniteProducts
public import SerrePositivity.InfinityCategories.Sheaves.CechPointElements
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：商の上の既存有限冪の Čech 図式を、元の底圏の指定余錐として読む。
方針：同じ Over の忘却と構造射を使い、各 Hom 値の余錐も同じ関手の像として保持する。
規約：HTT 6.2.2.6 の Čech 解消への通常圏の入力。有限冪を選び直さない。
使われ方：S8 の一般の局所同値の同じ Čech 増大。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [Category.{v} C] {P Q : C}
variable (f : P ⟶ Q) [HasFiniteProducts (Over Q)]

/-- 商の上の元の有限冪の Čech データ。 -/
abbrev relativeCechData : CategoryTheory.CechNerveData (Over.mk f) :=
  CategoryTheory.CechNerveData.ofFiniteProducts (Over.mk f)

/-- 同じ有限冪の図式を底圏で読み、添字だけを Hom の宇宙へ移す。 -/
abbrev relativeCechDiagram : AsSmall.{v} SimplexCategoryᵒᵖ ⥤ C :=
  AsSmall.down ⋙ (relativeCechData f).obj ⋙ Over.forget Q

/-- 元の構造射を全ての脚とする、商への指定 Čech 増大。 -/
def relativeCechCocone : Cocone (relativeCechDiagram f) where
  pt := Q
  ι :=
    { app := fun n => ((relativeCechData f).obj.obj (AsSmall.down.obj n)).hom
      naturality := fun i j θ => by
        change ((relativeCechData f).obj.map (AsSmall.down.map θ)).left ≫
          ((relativeCechData f).obj.obj (AsSmall.down.obj j)).hom =
            ((relativeCechData f).obj.obj (AsSmall.down.obj i)).hom ≫ 𝟙 Q
        rw [Category.comp_id]
        exact Over.w ((relativeCechData f).obj.map (AsSmall.down.map θ)) }

/-- 同じ指定余錐を Hom で評価する。 -/
abbrev relativeCechHomCocone (V : C) :=
  (coyoneda.obj (Opposite.op V)).mapCocone (relativeCechCocone f)

end SerrePositivity.InfinityCategories.Sheaves

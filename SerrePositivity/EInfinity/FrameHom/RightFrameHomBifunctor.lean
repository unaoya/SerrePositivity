module
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Frames.RightFrameFamily
public import SerrePositivity.EInfinity.FrameHom.MixedFrameSource

/-!
概要：元のright frame Homを始域にも反変な全関手としてまとめる。
方針：既存のcoyonedaと元のright frame図式へのwhiskeringを合成する。
規約：IS-W2 R02〜R03の既存Hom構成の全係数表示。元のframe・射を変更しない。
使われ方：固定始域ごとの比較と、始域の作用を区別して全自然性を照合する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 元のright frame Homを両変数で束ねた、同じcoyonedaの全関手。 -/
def rightFrameHomBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  coyoneda ⋙ Functor.whiskeringRight SimplexCategoryᵒᵖ C (Type v) ⋙
    (Functor.whiskeringLeft C (SimplexCategoryᵒᵖ ⥤ C) SSet.{v}).obj (rightFrameDiagram r)

/-- 始域を固定した値は、元の同じright frame Hom。 -/
theorem rightFrameHomBifunctor_obj (X : C) :
    (rightFrameHomBifunctor r).obj (Opposite.op X) = rightFrameHom r X := rfl

/-- 全関手の始域作用は元の射による前合成そのもの。 -/
theorem rightFrameHomBifunctor_map {X Y : C} (f : X ⟶ Y) :
    (rightFrameHomBifunctor r).map f.op =
      Functor.whiskerLeft (rightFrameDiagram r) (MixedFrame.rightSourceMap f) := rfl

/-- 元の通常Homも同じ二変数の全関手として読む。 -/
def ordinaryHomBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  coyoneda ⋙ Functor.whiskeringRight SimplexCategoryᵒᵖ C (Type v) ⋙
    (Functor.whiskeringLeft C (SimplexCategoryᵒᵖ ⥤ C) SSet.{v}).obj
      (Functor.const SimplexCategoryᵒᵖ)

/-- 元のframe単位は、始域の元の射の前合成についても厳密に自然。 -/
theorem rightFrameHomUnit_source {X Y : C} (f : X ⟶ Y) :
    ordinaryHomBifunctor.map f.op ≫ rightFrameHomUnit r X =
      rightFrameHomUnit r Y ≫ (rightFrameHomBifunctor r).map f.op := by
  apply NatTrans.ext
  funext Z
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro h
  change (f ≫ h) ≫ ((rightFrameUnit r).app Z).app n =
    f ≫ (h ≫ ((rightFrameUnit r).app Z).app n)
  exact Category.assoc _ _ _

end SerrePositivity.EInfinity.FrameHom

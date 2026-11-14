module
public import SerrePositivity.EInfinity.FrameHom.RightFrameHomBifunctor
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.RightMixedFamily

/-!
概要：元の混合frame比較の両変数の自然性を、一つの自然変換として束ねる。
方針：同じ関手的source frameの写像による前合成と、元のaugmentationを使う。
規約：IS-W2 R02〜R03の既存構成の自然性・合成則。新しいframeや比較は選ばない。
使われ方：全joint Hom比較の最初の二辺に、固定始域の比較をそのまま使う。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (q : CofibrantResolutionFamily (C := C) simplex)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 同じ関手的source frameとright frameからなる、元の混合Homの全関手。 -/
def rightMixedBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} where
  obj X := rightMixedFamily (q.atObject X.unop) r
  map f := Functor.whiskerLeft (rightFrameDiagram r)
    (MixedFrame.mixedSourceMap (q.obj.map f.unop))
  map_id X := by
    ext Y n h
    change (q.obj.map (𝟙 X.unop)).app n.unop ≫ h = h
    rw [q.obj.map_id]
    exact Category.id_comp _
  map_comp f g := by
    ext Y n h
    change (q.obj.map (g.unop ≫ f.unop)).app n.unop ≫ h =
      (q.obj.map g.unop).app n.unop ≫ ((q.obj.map f.unop).app n.unop ≫ h)
    rw [q.obj.map_comp]
    exact Category.assoc _ _ _

/-- 始域固定の値は元の同じ混合Hom。 -/
theorem rightMixedBifunctor_obj (X : C) :
    (rightMixedBifunctor q r).obj (Opposite.op X) = rightMixedFamily (q.atObject X) r := rfl

/-- 同じsource frame Homを始域に関しても束ねる。 -/
def sourceFrameHomBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{v} :=
  q.obj.op ⋙ cosimplicialHomBifunctor

/-- 元の混合左比較を両変数で束ねた全自然変換。 -/
def rightMixedLeftBifunctorMap : sourceFrameHomBifunctor q ⟶ rightMixedBifunctor q r where
  app X := rightMixedLeft (q.atObject X.unop) r
  naturality X Y f := by
    ext Z n h
    change ((q.obj.map f.unop).app n.unop ≫ h) ≫
        ((rightFrameUnit r).app Z).app n =
      (q.obj.map f.unop).app n.unop ≫ (h ≫ ((rightFrameUnit r).app Z).app n)
    exact Category.assoc _ _ _

/-- 元の混合右比較を両変数で束ねた全自然変換。 -/
def rightMixedRightBifunctorMap : rightFrameHomBifunctor r ⟶ rightMixedBifunctor q r where
  app X := rightMixedRight (q.atObject X.unop) r
  naturality X Y f := by
    ext Z n h
    change (q.augmentation.app Y.unop).app n.unop ≫ (f.unop ≫ h) =
      (q.obj.map f.unop).app n.unop ≫ ((q.augmentation.app X.unop).app n.unop ≫ h)
    have hn : (q.obj.map f.unop).app n.unop ≫
        (q.augmentation.app X.unop).app n.unop =
      (q.augmentation.app Y.unop).app n.unop ≫ f.unop :=
      congr_app (q.augmentation.naturality f.unop) n.unop
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ h) hn).symm.trans (Category.assoc _ _ _))

/-- 左比較の固定始域での成分は、元の比較そのもの。 -/
theorem rightMixedLeftBifunctorMap_app (X : C) :
    (rightMixedLeftBifunctorMap q r).app (Opposite.op X) =
      rightMixedLeft (q.atObject X) r := rfl

/-- 右比較の固定始域での成分も、元の比較そのもの。 -/
theorem rightMixedRightBifunctorMap_app (X : C) :
    (rightMixedRightBifunctorMap q r).app (Opposite.op X) =
      rightMixedRight (q.atObject X) r := rfl

end SerrePositivity.EInfinity.FrameHom

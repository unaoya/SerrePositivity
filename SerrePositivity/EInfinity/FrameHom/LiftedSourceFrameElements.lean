module
public import SerrePositivity.EInfinity.FrameHom.SourceFrameArrowElements
public import SerrePositivity.EInfinity.FrameHom.TotalElementsNativeClassification

/-!
概要：同じ全source-frame係数の宇宙持ち上げの全要素を、元の射の全要素へ戻す。
方針：元のAsSmallのdownと係数のULift.downを全対象・全射で適用する。
規約：元の単体次数・ラベル・両変数の射を保つ。
使われ方：BEの同じ全source-frameの射を元のtwisted pairingへ送る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)

/-- 同じ両変数の添字を、同じHom係数の宇宙に揃える。 -/
abbrev liftedSourceFrameIndex := AsSmall.{max u v} (Cᵒᵖ × C)

/-- 元の両変数の全source-frame Homに、同じ添字と係数の持ち上げを施す。 -/
def liftedSourceFrameCoefficients : liftedSourceFrameIndex (C := C) ⥤ SSet.{max u v} :=
  AsSmall.down ⋙ Functor.uncurry.obj (resolutionHom Q R) ⋙ SSet.uliftFunctor.{max u v,v}

/-- 元の持ち上げた全要素を、同じ元のsource-frameの射の全要素へ戻す。 -/
def liftedSourceFrameElementsDown :
    SimplicialTotalElements (liftedSourceFrameCoefficients Q R) ⥤ SourceFrameArrowElements Q R where
  obj X := { obj := (AsSmall.down.obj X.obj.1, X.obj.2), val := X.val.down }
  map f := { hom := (AsSmall.down.map f.hom.1, f.hom.2)
             map_val := congrArg ULift.down f.map_val }
  map_id X := by
    apply Functor.Elements.Hom.ext
    rfl
  map_comp f g := by
    apply Functor.Elements.Hom.ext
    rfl

/-- 同じdownは、元の両変数と元の単体次数をそのまま回収する。 -/
theorem liftedSourceFrameElementsDown_parameters :
    liftedSourceFrameElementsDown Q R ⋙ sourceFrameArrowParameters Q R =
      Functor.Elements.π (Functor.uncurry.obj (liftedSourceFrameCoefficients Q R)) ⋙
        (AsSmall.down.prod (𝟭 SimplexCategoryᵒᵖ)) := rfl

/-- 同じdownで回収するラベルは、元のULiftされた射のdownそのもの。 -/
theorem liftedSourceFrameElementsDown_value
    (X : SimplicialTotalElements (liftedSourceFrameCoefficients Q R)) :
    sourceFrameArrowValue Q R ((liftedSourceFrameElementsDown Q R).obj X) = X.val.down := rfl
end SerrePositivity.EInfinity.FrameHom
